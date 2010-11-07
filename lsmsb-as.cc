
#line 1 "lsmsb-as.rl"
#include <string>
#include <vector>
#include <map>

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include <unistd.h>
#include <fcntl.h>
#include <errno.h>

#include <assert.h>
#include <stdlib.h>
#define GFP_KERNEL 0
#define BUG_ON(x) assert(!(x))

uint8_t* kmalloc(size_t size, int unused) {
  return (uint8_t*) malloc(size);
}
void kfree(void* heap) { free(heap); }

struct lsmsb_value {
	uint8_t *data;
	uint32_t value;
};

struct lsmsb_filter {
	unsigned num_operations;
	unsigned num_spill_slots;
	unsigned num_constants;
	uint32_t *operations;
	struct lsmsb_value constants[0];
};

#define LSMSB_NUM_REGISTERS 16
// This is the maximum number of operations in a filter. Note that the code
// assumes that this value fits in a uint16_t with a couple of values to spare.
#define LSMSB_FILTER_OPS_MAX 32768
#define LSMSB_SPILL_SLOTS_MAX 32
#define LSMSB_CONSTANTS_MAX 256
#define LSMSB_CONSTANT_LENGTH_MAX 512

enum lsmsb_filter_code {
	LSMSB_FILTER_CODE_DENTRY_OPEN = 0,
	LSMSB_FILTER_CODE_SOCKET_CREATE,
	LSMSB_FILTER_CODE_SOCKET_CONNECT,
	LSMSB_FILTER_CODE_MAX,  // not a real filter code
};

enum lsmsb_opcode {
	LSMSB_OPCODE_MOV = 0,
	LSMSB_OPCODE_LDI,
	LSMSB_OPCODE_LDC,
	LSMSB_OPCODE_RET,
	LSMSB_OPCODE_JMP,
	LSMSB_OPCODE_SPILL,
	LSMSB_OPCODE_UNSPILL,
	LSMSB_OPCODE_JNZ,
	LSMSB_OPCODE_JZ,
	LSMSB_OPCODE_EQ,
	LSMSB_OPCODE_NE,
	LSMSB_OPCODE_GT,
	LSMSB_OPCODE_LT,
	LSMSB_OPCODE_GTE,
	LSMSB_OPCODE_LTE,
	LSMSB_OPCODE_AND,
	LSMSB_OPCODE_OR,
	LSMSB_OPCODE_XOR,
	LSMSB_OPCODE_ISPREFIXOF,
};

static inline enum lsmsb_opcode lsmsb_op_opcode_get(uint32_t op)
{
	return (enum lsmsb_opcode) (op >> 24);
}

static inline char lsmsb_opcode_falls_through(enum lsmsb_opcode opcode)
{
	return opcode != LSMSB_OPCODE_RET &&
	       opcode != LSMSB_OPCODE_JMP;
}

static inline unsigned lsmsb_opcode_is_jump(enum lsmsb_opcode opcode)
{
	return opcode == LSMSB_OPCODE_JMP ||
	       opcode == LSMSB_OPCODE_JNZ ||
	       opcode == LSMSB_OPCODE_JZ;
}

static inline unsigned lsmsb_op_jump_length(uint32_t op)
{
	const unsigned opcode = op >> 24;
	if (opcode == LSMSB_OPCODE_JMP ||
	    opcode == LSMSB_OPCODE_JNZ ||
	    opcode == LSMSB_OPCODE_JZ)
		return op & 0xff;
	return 0;
}

static inline unsigned lsmsb_op_reg1_get(uint32_t op)
{
	return (op >> 20) & 0xf;
}

static inline unsigned lsmsb_op_reg2_get(uint32_t op)
{
	return (op >> 16) & 0xf;
}

static inline unsigned lsmsb_op_reg3_get(uint32_t op)
{
	return (op >> 12) & 0xf;
}

static inline unsigned lsmsb_op_spill1_get(uint32_t op)
{
	return (op >> 16) & 0xff;
}

static inline unsigned lsmsb_op_spill2_get(uint32_t op)
{
	return (op >> 12) & 0xff;
}

static inline unsigned lsmsb_op_constant1_get(uint32_t op)
{
	return op & 0xff;
}

static inline unsigned lsmsb_op_imm_get(uint32_t op)
{
	return op & 0xfffff;
}

static inline void lsmsb_value_u32_set(struct lsmsb_value *value, unsigned v)
{
	value->data = NULL;
	value->value = v;
}

/* This is the magic unset value in the predecessor table. This value must be
 * all ones because we clear the table with a memset. */
#define LSMSB_PREDECESSOR_TABLE_INVAL 0xffff
/* This is a magic value in the predecessor table which marks an overflow. */
#define LSMSB_PREDECESSOR_TABLE_OVERFLOW (LSMSB_FILTER_OPS_MAX + 1)
/* This is the number of predecessors that we record, per row, before
 * overflowing */
#define LSMSB_PREDECESSOR_TABLE_WIDTH 2

static void lsmsb_predecessor_table_append(uint16_t *ptable, unsigned target,
					   unsigned source)
{
	uint16_t *row = &ptable[target * LSMSB_PREDECESSOR_TABLE_WIDTH];
	unsigned i;

	for (i = 0; i < LSMSB_PREDECESSOR_TABLE_WIDTH; ++i) {
		if (row[i] == LSMSB_PREDECESSOR_TABLE_OVERFLOW)
			return;  // this is already an overflow row
		if (row[i] == LSMSB_PREDECESSOR_TABLE_INVAL) {
			row[i] = source;
			return;
		}
	}

	/* we reached the end of the table without a spare slot. We have to mark
	   the row as overflowed. */
	row[0] = LSMSB_PREDECESSOR_TABLE_OVERFLOW;
}

static char lsmsb_predecessor_table_fill(uint16_t *ptable, const uint32_t *ops, unsigned num_ops)
{
	unsigned i;

	if (num_ops == 0)
		return 1;

	memset(ptable, 0xff, sizeof(uint16_t) * num_ops * LSMSB_PREDECESSOR_TABLE_WIDTH);

	/* First we deal with all the elements except the last. */
	for (i = 0; i < num_ops - 1; ++i) {
		const uint32_t op = ops[i];
		const enum lsmsb_opcode opcode = lsmsb_op_opcode_get(op);

		if (lsmsb_opcode_falls_through(opcode))
			lsmsb_predecessor_table_append(ptable, i + 1, i);
		if (lsmsb_opcode_is_jump(opcode)) {
			/* 0 <= i, jumplength <= 0xffff */
			const unsigned target = i + lsmsb_op_jump_length(op);
			if (target == i)
				return 0;  /* zero length jump */
			if (target >= num_ops)
				return 0;  /* tried to jump off the end */
			lsmsb_predecessor_table_append(ptable, target, i);
		}
	}

	/* Now deal with the last operation. */
	if (lsmsb_op_opcode_get(ops[num_ops - 1]) != LSMSB_OPCODE_RET)
		return 0;

	return 1;
}

enum lsmsb_type {
	LSMSB_TYPE_UNDEF = 0,
	LSMSB_TYPE_U32,
	LSMSB_TYPE_BYTESTRING,
	LSMSB_TYPE_CONFLICTING,
};

static inline char lsmsb_type_is_value(enum lsmsb_type type)
{
	return type == LSMSB_TYPE_U32 || type == LSMSB_TYPE_BYTESTRING;
}

static inline enum lsmsb_type lsmsb_constant_type_get(const struct lsmsb_value *v)
{
	return v->data ? LSMSB_TYPE_BYTESTRING : LSMSB_TYPE_U32;
}

static inline unsigned lsmsb_filter_tva_width(const struct lsmsb_filter *filter)
{
	return (LSMSB_NUM_REGISTERS + filter->num_spill_slots + 3) / 4;
}

static inline enum lsmsb_type lsmsb_type_vector_reg_get(uint8_t *vector, unsigned reg)
{
	const unsigned byte = reg >> 2;
	const unsigned index = reg & 3;

	return (enum lsmsb_type) ((vector[byte] >> (6 - (index * 2))) & 3);
}

static inline enum lsmsb_type lsmsb_type_vector_spill_get(uint8_t *vector, unsigned slot)
{
	return lsmsb_type_vector_reg_get(vector, slot + LSMSB_NUM_REGISTERS);
}

static inline void lsmsb_type_vector_reg_set(uint8_t *vector, unsigned reg,
                                             enum lsmsb_type newtype)
{
	const unsigned byte = reg >> 2;
	const unsigned index = reg & 3;
	static const uint8_t masks[4] = { 0x3f, 0xcf, 0xf3, 0xfc };
	const uint8_t new_value = (vector[byte] & masks[index]) |
	                          newtype << (6 - (index * 2));
	vector[byte] = new_value;
}

static inline void lsmsb_type_vector_spill_set(uint8_t *vector, unsigned slot,
                                               enum lsmsb_type newtype)
{
	lsmsb_type_vector_reg_set(vector, slot + LSMSB_NUM_REGISTERS, newtype);
}

static char lsmsb_op_is_predecessor_of(const uint32_t *ops, unsigned i,
                                       unsigned target) {
	const uint32_t op = ops[i];
	const enum lsmsb_opcode opcode = lsmsb_op_opcode_get(op);
	
	if (i == target - 1 &&
	    lsmsb_opcode_falls_through(opcode)) {
		return 1;
	}

	if (lsmsb_opcode_is_jump(opcode) &&
	    lsmsb_op_jump_length(op) + i == target) {
		return 1;
	}

	return 0;
}

static void lsmsb_type_vector_unify(uint8_t *a, const uint8_t *b, unsigned bytelen)
{
	unsigned offset = 0;
	while (bytelen >= 4) {
		uint32_t u = *((uint32_t *) (a + offset));
		uint32_t v = *((uint32_t *) (b + offset));
		uint32_t x = u ^ v;
		uint32_t left = x & 0xaaaaaaaau, right = x & 0x55555555;
		uint32_t result = (left | (left >> 1)) | (right | (right << 1));
		*((uint32_t *) (a + offset)) |= result;

		offset += 4;
		bytelen -= 4;
	}

	while (bytelen) {
		uint8_t u = a[offset];
		uint8_t v = b[offset];
		uint8_t x = u ^ v;
		uint32_t left = x & 0xaa, right = x & 0x55;
		uint32_t result = (left | (left >> 1)) | (right | (right << 1));
		a[offset] |= result;

		offset++;
		bytelen--;
	}
}

static char lsmsb_op_type_vector_update(uint8_t *tv, uint32_t op,
					const struct lsmsb_value *constants,
					unsigned num_constants,
					unsigned num_spills) {
	const enum lsmsb_opcode opcode = lsmsb_op_opcode_get(op);
	unsigned reg1, reg2, reg3;
	enum lsmsb_type type1, type2, type3;
	unsigned c1, s1;

	switch (opcode) {
	case LSMSB_OPCODE_MOV:
		reg1 = lsmsb_op_reg1_get(op);
		reg2 = lsmsb_op_reg2_get(op);
		type2 = lsmsb_type_vector_reg_get(tv, reg2);
		if (!lsmsb_type_is_value(type2))
			return 0;
		lsmsb_type_vector_reg_set(tv, reg1, type2);
		return 1;
	case LSMSB_OPCODE_LDI:
		reg1 = lsmsb_op_reg1_get(op);
		lsmsb_type_vector_reg_set(tv, reg1, LSMSB_TYPE_U32);
		return 1;
	case LSMSB_OPCODE_LDC:
		reg1 = lsmsb_op_reg1_get(op);
		c1 = lsmsb_op_constant1_get(op);
		if (c1 >= num_constants)
			return 0;
		type1 = lsmsb_constant_type_get(&constants[c1]);
		lsmsb_type_vector_reg_set(tv, reg1, type1);
		return 1;
	case LSMSB_OPCODE_RET:
		reg1 = lsmsb_op_reg1_get(op);
		if (lsmsb_type_vector_reg_get(tv, reg1) != LSMSB_TYPE_U32)
			return 0;
		return 1;
	case LSMSB_OPCODE_JMP:
		return 1;
	case LSMSB_OPCODE_SPILL:
		s1 = lsmsb_op_spill1_get(op);
		if (s1 >= num_spills)
			return 0;
		reg1 = lsmsb_op_reg3_get(op);
		type1 = lsmsb_type_vector_reg_get(tv, reg1);
		if (!lsmsb_type_is_value(type1))
			return 0;
		lsmsb_type_vector_spill_set(tv, s1, type1);
		return 1;
	case LSMSB_OPCODE_UNSPILL:
		reg1 = lsmsb_op_reg1_get(op);
		s1 = lsmsb_op_spill2_get(op);
		if (s1 >= num_spills)
			return 0;
		type1 = lsmsb_type_vector_spill_get(tv, s1);
		if (!lsmsb_type_is_value(type1))
			return 0;
		lsmsb_type_vector_reg_set(tv, reg1, type1);
		return 1;
	case LSMSB_OPCODE_JNZ:
	case LSMSB_OPCODE_JZ:
		reg1 = lsmsb_op_reg1_get(op);
		if (lsmsb_type_vector_reg_get(tv, reg1) != LSMSB_TYPE_U32)
			return 0;
		return 1;
	case LSMSB_OPCODE_EQ:
	case LSMSB_OPCODE_NE:
	case LSMSB_OPCODE_GT:
	case LSMSB_OPCODE_LT:
	case LSMSB_OPCODE_GTE:
	case LSMSB_OPCODE_LTE:
	case LSMSB_OPCODE_AND:
	case LSMSB_OPCODE_OR:
	case LSMSB_OPCODE_XOR:
		reg1 = lsmsb_op_reg1_get(op);
		reg2 = lsmsb_op_reg2_get(op);
		reg3 = lsmsb_op_reg3_get(op);
		type2 = lsmsb_type_vector_reg_get(tv, reg2);
		type3 = lsmsb_type_vector_reg_get(tv, reg3);
		if (type2 != LSMSB_TYPE_U32 || type3 != LSMSB_TYPE_U32)
			return 0;
		lsmsb_type_vector_reg_set(tv, reg1, LSMSB_TYPE_U32);
		return 1;
	case LSMSB_OPCODE_ISPREFIXOF:
		reg1 = lsmsb_op_reg1_get(op);
		reg2 = lsmsb_op_reg2_get(op);
		reg3 = lsmsb_op_reg3_get(op);
		type2 = lsmsb_type_vector_reg_get(tv, reg2);
		type3 = lsmsb_type_vector_reg_get(tv, reg3);
		if (type2 != LSMSB_TYPE_BYTESTRING ||
		    type3 != LSMSB_TYPE_BYTESTRING)
			return 0;
		lsmsb_type_vector_reg_set(tv, reg1, LSMSB_TYPE_U32);
		return 1;
	default:
		return 0;
	}
}

static char lsmsb_type_vector_array_fill(uint8_t *tva,
					 const uint16_t *ptable,
					 const uint8_t *context_tv,
					 const struct lsmsb_filter *filter) {
	const unsigned tva_width = lsmsb_filter_tva_width(filter);
	const uint32_t *ops = filter->operations;
	unsigned i, j;

	if (filter->num_operations == 0)
		return 1;

	memset(tva, 0, tva_width);  /* set the first row to LSMSB_TYPE_UNDEF */
	memcpy(tva, context_tv, LSMSB_NUM_REGISTERS / 4);

	if (!lsmsb_op_type_vector_update(tva, ops[0], filter->constants,
					 filter->num_constants,
					 filter->num_spill_slots)) {
		return 0;
	}

	for (i = 1; i < filter->num_operations; ++i) {
		const uint16_t *ptable_row =
			&ptable[i * LSMSB_PREDECESSOR_TABLE_WIDTH];
		uint8_t *tva_row = tva + i * tva_width;
		char found_predecessor = 0;

		if (ptable_row[0] == LSMSB_PREDECESSOR_TABLE_OVERFLOW) {
			for (j = 0; j < i; ++j) {
				if (lsmsb_op_is_predecessor_of(ops, j, i)) {
					if (!found_predecessor) {
						memcpy(tva_row,
						       tva + j * tva_width,
						       tva_width);
						found_predecessor = 1;
						continue;
					}

					lsmsb_type_vector_unify(
						tva_row,
						tva + j * tva_width,
						tva_width);
				}
			}

			if (!found_predecessor)
				return 0;  // shouldn't ever happen
		} else {
			for (j = 0; j < LSMSB_PREDECESSOR_TABLE_WIDTH; ++j) {
				const unsigned p = ptable_row[j];
				const uint8_t *tva_row_p = tva + p * tva_width;
				if (p == LSMSB_PREDECESSOR_TABLE_INVAL)
					break;
				if (!found_predecessor) {
					memcpy(tva_row, tva_row_p, tva_width);
					found_predecessor = 1;
					continue;
				}

				lsmsb_type_vector_unify(tva_row, tva_row_p,
							tva_width);
			}

			if (!found_predecessor)
				return 0;  // Dead code.
		}

		if (!lsmsb_op_type_vector_update(tva_row, ops[i],
						 filter->constants,
						 filter->num_constants,
						 filter->num_spill_slots)) {
			return 0;
		}
	}

	return 1;
}

struct filter_context {
  const char *filter_name;
  const char *type_string;
};

static const struct filter_context filter_contexts[] = {
  {"dentry-open", "BI"}, // LSMSB_FILTER_CODE_DENTRY_OPEN
  {"socket-create", "IIII"}, // LSMSB_FILTER_CODE_SOCKET_CREATE
  {"socket-connect", "IIIIIB"}, // LSMSB_FILTER_CODE_SOCKET_CONNECT
  {NULL, NULL}
};

static uint8_t *type_vector_for_filter(const struct lsmsb_filter *filter,
				       const char *context_string)
{
	uint8_t *tv = kmalloc(lsmsb_filter_tva_width(filter), GFP_KERNEL);
	unsigned i;

	if (!tv)
		return NULL;
	memset(tv, 0, lsmsb_filter_tva_width(filter));
	
	for (i = 0; ; ++i) {
		switch (context_string[i]) {
		case 0:
			return tv;
		case 'B':
			lsmsb_type_vector_reg_set(tv, i, LSMSB_TYPE_BYTESTRING);
			break;
		case 'I':
			lsmsb_type_vector_reg_set(tv, i, LSMSB_TYPE_U32);
			break;
		default:
			BUG_ON(1);
			return tv;
		}
	}
}

static int lsmsb_filter_typecheck(const struct lsmsb_filter *filter,
			   const uint8_t *context_type_vector)
{
	const unsigned tva_width = lsmsb_filter_tva_width(filter);
	uint16_t *predecessor_table;
	uint8_t *type_vector_array;
	int return_code = -EINVAL;

	predecessor_table = (uint16_t*) kmalloc(
		filter->num_operations *
		LSMSB_PREDECESSOR_TABLE_WIDTH *
		sizeof(uint16_t), GFP_KERNEL);
	if (!predecessor_table)
		return -ENOMEM;
	type_vector_array = kmalloc(filter->num_operations *
				    tva_width, GFP_KERNEL);
	if (!type_vector_array) {
		kfree(predecessor_table);
		return -ENOMEM;
	}

	if (!lsmsb_predecessor_table_fill(predecessor_table, filter->operations,
					  filter->num_operations)) {
		goto exit;
	}

	if (!lsmsb_type_vector_array_fill(type_vector_array, predecessor_table,
					  context_type_vector, filter)) {
		goto exit;
	}

	return_code = 0;

exit:
	kfree(type_vector_array);
	kfree(predecessor_table);
	return return_code;
}

struct lsmsb_filter_wire {
	uint32_t filter_code;
	uint32_t num_operations;
	uint32_t num_spill_slots;
	uint32_t num_constants;
};

struct lsmsb_constant_wire {
	uint32_t type;  // 0 for integer, 1 for bytestring
	uint32_t value;
	/* In the case of a bytestring, the bytes follow and |value| is the length */
};

static bool writea(int fd, const void *in_data, size_t length)
{
  size_t done = 0;
  const uint8_t *data = reinterpret_cast<const uint8_t*>(in_data);

  while (done < length) {
    ssize_t result;

    do {
      result = write(fd, data + done, length - done);
    } while (result == -1 && errno == EINTR);

    if (result < 0)
      return false;
    done += result;
  }

  return true;
}

static uint8_t
from_hex_char(char h) {
  if (h >= '0' && h <= '9')
    return h - '0';
  if (h >= 'a' && h <= 'f')
    return (h - 'a') + 10;
  return (h - 'A') + 10;
}

static std::string
hex_parse(const std::string &in) {
  uint8_t *bytes = (uint8_t *) malloc(in.size() / 2);

  for (size_t i = 0; i < in.size() / 2; ++i) {
    bytes[i] = (from_hex_char(in[i*2]) << 4) |
                from_hex_char(in[i*2 + 1]);
  }

  std::string ret((const char *) bytes, in.size() / 2);
  free(bytes);
  return ret;
}

static uint32_t
u32_parse(const std::string &in) {
  return strtoul(in.c_str(), NULL, 0);
}

static uint32_t
imm_check(uint32_t v) {
  if ((v & 0xfffff) != v) {
    fprintf(stderr, "Immediate value too large: %d\n", v);
    abort();
  }

  return v;
}

static uint32_t
reg_parse(const std::string &r, uint32_t max) {
  uint32_t n = strtoul(r.c_str() + 1, NULL, 10);
  if (n >= max) {
    fprintf(stderr, "Invalid register: %s\n", r.c_str());
    abort();
  }
  return n;
}


#line 641 "lsmsb-as.cc"
static const char _as_actions[] = {
	0, 1, 0, 1, 1, 1, 2, 1, 
	3, 1, 4, 1, 5, 1, 6, 1, 
	7, 1, 8, 1, 9, 1, 10, 1, 
	11, 1, 12, 1, 13, 1, 14, 1, 
	15, 1, 16, 1, 17, 1, 18, 1, 
	19, 1, 20, 1, 21, 1, 22, 1, 
	23, 1, 24, 1, 25, 1, 26, 1, 
	27, 1, 28, 1, 29, 1, 30, 1, 
	31, 1, 32, 1, 33, 1, 34, 1, 
	35, 1, 36, 1, 37, 2, 0, 1, 
	2, 0, 3, 2, 1, 5, 2, 1, 
	6, 2, 15, 3, 2, 16, 1, 2, 
	17, 1, 2, 18, 1, 2, 19, 1, 
	2, 20, 1, 2, 21, 1, 2, 22, 
	1, 2, 23, 1, 2, 24, 1, 2, 
	25, 1, 2, 26, 1, 2, 27, 1, 
	2, 28, 1, 2, 29, 1, 2, 30, 
	1, 2, 32, 1, 2, 35, 1, 2, 
	36, 1
};

static const short _as_key_offsets[] = {
	0, 0, 2, 2, 3, 4, 5, 6, 
	7, 8, 9, 10, 20, 30, 43, 48, 
	53, 55, 55, 56, 57, 58, 78, 98, 
	104, 113, 132, 151, 153, 153, 154, 155, 
	156, 157, 158, 163, 168, 173, 175, 175, 
	176, 177, 178, 180, 187, 192, 197, 202, 
	207, 209, 209, 210, 211, 212, 214, 221, 
	226, 231, 236, 241, 243, 243, 244, 245, 
	246, 248, 255, 260, 265, 267, 267, 268, 
	269, 270, 289, 290, 295, 296, 302, 307, 
	308, 309, 310, 311, 312, 313, 314, 315, 
	316, 321, 324, 325, 330, 335, 340, 346, 
	359, 361, 361, 362, 363, 364, 365, 370, 
	375, 380, 382, 382, 383, 384, 385, 387, 
	394, 399, 404, 406, 406, 407, 408, 409, 
	414, 416, 418, 423, 428, 433, 435, 435, 
	436, 437, 438, 440, 443, 453, 463, 476, 
	478, 478, 479, 480, 481, 486, 491, 496, 
	498, 498, 499, 500, 501, 503, 506, 513, 
	520, 522, 522, 523, 524, 525, 533, 540, 
	546, 557, 564, 570, 575, 576, 577, 582, 
	587, 592, 594, 594, 595, 596, 597, 599, 
	602, 607, 612, 614, 614, 615, 616, 617, 
	619, 626, 627, 632, 633, 638, 639, 640, 
	645, 650, 655, 657, 657, 658, 659, 660, 
	662, 669, 670, 671, 672, 673, 678, 683, 
	688, 690, 690, 691, 692, 693, 695, 698, 
	699, 700, 701, 702, 703, 704, 709, 714, 
	719, 721, 721, 722, 723, 724, 726, 729, 
	734, 739, 741, 741, 742, 743, 744, 746, 
	753, 754, 755, 760, 762, 762, 763, 764, 
	765, 767, 767, 768, 769, 770, 772, 772, 
	773, 774, 775, 776, 777, 778, 779, 780, 
	781, 782, 783, 788, 793, 795, 795, 796, 
	797, 798, 809, 820, 833, 838, 843, 845, 
	845, 846, 847, 848, 857, 866, 867, 868, 
	873, 878, 880, 880, 881, 882, 883, 885, 
	885, 886, 887, 888, 896, 903, 909, 920, 
	927, 928, 935, 942, 944, 944, 945, 946, 
	947, 966, 985, 987, 987, 988, 989, 990, 
	991, 992, 993, 994, 1000, 1001, 1002, 1003, 
	1004, 1005, 1012, 1019, 1021, 1021, 1022, 1023, 
	1024, 1032, 1037, 1042, 1044, 1044, 1045, 1046, 
	1047, 1054, 1060, 1071, 1078, 1080, 1080, 1081, 
	1082, 1083, 1088
};

static const char _as_trans_keys[] = {
	42, 47, 42, 47, 10, 105, 108, 116, 
	101, 114, 9, 10, 32, 45, 47, 95, 
	65, 90, 97, 122, 9, 10, 32, 45, 
	47, 95, 65, 90, 97, 122, 9, 10, 
	32, 45, 47, 95, 123, 48, 57, 65, 
	90, 97, 122, 9, 10, 32, 47, 123, 
	9, 10, 32, 47, 123, 42, 47, 42, 
	47, 10, 9, 10, 32, 35, 47, 97, 
	99, 101, 103, 105, 106, 108, 109, 110, 
	111, 114, 115, 117, 120, 125, 9, 10, 
	32, 35, 47, 97, 99, 101, 103, 105, 
	106, 108, 109, 110, 111, 114, 115, 117, 
	120, 125, 45, 95, 65, 90, 97, 122, 
	45, 58, 95, 48, 57, 65, 90, 97, 
	122, 9, 10, 32, 35, 47, 97, 101, 
	103, 105, 106, 108, 109, 110, 111, 114, 
	115, 117, 120, 125, 9, 10, 32, 35, 
	47, 97, 101, 103, 105, 106, 108, 109, 
	110, 111, 114, 115, 117, 120, 125, 42, 
	47, 42, 47, 10, 110, 100, 9, 10, 
	32, 47, 114, 9, 10, 32, 47, 114, 
	9, 10, 32, 47, 114, 42, 47, 42, 
	47, 10, 48, 57, 9, 10, 32, 44, 
	47, 48, 57, 9, 10, 32, 44, 47, 
	9, 10, 32, 44, 47, 9, 10, 32, 
	47, 114, 9, 10, 32, 47, 114, 42, 
	47, 42, 47, 10, 48, 57, 9, 10, 
	32, 44, 47, 48, 57, 9, 10, 32, 
	44, 47, 9, 10, 32, 44, 47, 9, 
	10, 32, 47, 114, 9, 10, 32, 47, 
	114, 42, 47, 42, 47, 10, 48, 57, 
	9, 10, 32, 47, 59, 48, 57, 9, 
	10, 32, 47, 59, 9, 10, 32, 47, 
	59, 42, 47, 42, 47, 10, 9, 10, 
	32, 35, 47, 97, 101, 103, 105, 106, 
	108, 109, 110, 111, 114, 115, 117, 120, 
	125, 113, 9, 10, 32, 47, 114, 116, 
	9, 10, 32, 47, 101, 114, 9, 10, 
	32, 47, 114, 115, 112, 114, 101, 102, 
	105, 120, 111, 102, 9, 10, 32, 47, 
	114, 109, 110, 122, 112, 9, 10, 32, 
	35, 47, 9, 10, 32, 35, 47, 9, 
	10, 32, 35, 47, 45, 95, 65, 90, 
	97, 122, 9, 10, 32, 45, 47, 59, 
	95, 48, 57, 65, 90, 97, 122, 42, 
	47, 42, 47, 10, 122, 9, 10, 32, 
	47, 114, 9, 10, 32, 47, 114, 9, 
	10, 32, 47, 114, 42, 47, 42, 47, 
	10, 48, 57, 9, 10, 32, 44, 47, 
	48, 57, 9, 10, 32, 44, 47, 9, 
	10, 32, 44, 47, 42, 47, 42, 47, 
	10, 9, 10, 32, 47, 114, 100, 116, 
	99, 105, 9, 10, 32, 47, 114, 9, 
	10, 32, 47, 114, 9, 10, 32, 47, 
	114, 42, 47, 42, 47, 10, 48, 57, 
	44, 48, 57, 9, 10, 32, 45, 47, 
	95, 65, 90, 97, 122, 9, 10, 32, 
	45, 47, 95, 65, 90, 97, 122, 9, 
	10, 32, 45, 47, 59, 95, 48, 57, 
	65, 90, 97, 122, 42, 47, 42, 47, 
	10, 9, 10, 32, 47, 114, 9, 10, 
	32, 47, 114, 9, 10, 32, 47, 114, 
	42, 47, 42, 47, 10, 48, 57, 44, 
	48, 57, 9, 10, 32, 47, 48, 49, 
	57, 9, 10, 32, 47, 48, 49, 57, 
	42, 47, 42, 47, 10, 9, 10, 32, 
	47, 59, 120, 48, 55, 9, 10, 32, 
	47, 59, 48, 55, 48, 57, 65, 70, 
	97, 102, 9, 10, 32, 47, 59, 48, 
	57, 65, 70, 97, 102, 9, 10, 32, 
	47, 59, 48, 57, 9, 10, 32, 47, 
	101, 114, 9, 10, 32, 47, 114, 111, 
	118, 9, 10, 32, 47, 114, 9, 10, 
	32, 47, 114, 9, 10, 32, 47, 114, 
	42, 47, 42, 47, 10, 48, 57, 44, 
	48, 57, 9, 10, 32, 47, 114, 9, 
	10, 32, 47, 114, 42, 47, 42, 47, 
	10, 48, 57, 9, 10, 32, 47, 59, 
	48, 57, 101, 9, 10, 32, 47, 114, 
	114, 9, 10, 32, 47, 114, 101, 116, 
	9, 10, 32, 47, 114, 9, 10, 32, 
	47, 114, 9, 10, 32, 47, 114, 42, 
	47, 42, 47, 10, 48, 57, 9, 10, 
	32, 47, 59, 48, 57, 112, 105, 108, 
	108, 9, 10, 32, 47, 115, 9, 10, 
	32, 47, 115, 9, 10, 32, 47, 115, 
	42, 47, 42, 47, 10, 48, 57, 44, 
	48, 57, 110, 115, 112, 105, 108, 108, 
	9, 10, 32, 47, 114, 9, 10, 32, 
	47, 114, 9, 10, 32, 47, 114, 42, 
	47, 42, 47, 10, 48, 57, 44, 48, 
	57, 9, 10, 32, 47, 115, 9, 10, 
	32, 47, 115, 42, 47, 42, 47, 10, 
	48, 57, 9, 10, 32, 47, 59, 48, 
	57, 111, 114, 9, 10, 32, 47, 114, 
	42, 47, 42, 47, 10, 42, 47, 42, 
	47, 10, 42, 47, 42, 47, 10, 111, 
	110, 115, 116, 97, 110, 116, 115, 9, 
	10, 32, 47, 123, 9, 10, 32, 47, 
	123, 42, 47, 42, 47, 10, 9, 10, 
	32, 45, 47, 95, 125, 65, 90, 97, 
	122, 9, 10, 32, 45, 47, 95, 125, 
	65, 90, 97, 122, 9, 10, 32, 45, 
	47, 61, 95, 48, 57, 65, 90, 97, 
	122, 9, 10, 32, 47, 61, 9, 10, 
	32, 47, 61, 42, 47, 42, 47, 10, 
	9, 10, 32, 34, 47, 48, 120, 49, 
	57, 9, 10, 32, 34, 47, 48, 120, 
	49, 57, 34, 34, 9, 10, 32, 47, 
	59, 9, 10, 32, 47, 59, 42, 47, 
	42, 47, 10, 42, 47, 42, 47, 10, 
	9, 10, 32, 47, 59, 120, 48, 55, 
	9, 10, 32, 47, 59, 48, 55, 48, 
	57, 65, 70, 97, 102, 9, 10, 32, 
	47, 59, 48, 57, 65, 70, 97, 102, 
	9, 10, 32, 47, 59, 48, 57, 34, 
	34, 48, 57, 65, 70, 97, 102, 34, 
	48, 57, 65, 70, 97, 102, 42, 47, 
	42, 47, 10, 9, 10, 32, 35, 47, 
	97, 101, 103, 105, 106, 108, 109, 110, 
	111, 114, 115, 117, 120, 125, 9, 10, 
	32, 35, 47, 97, 101, 103, 105, 106, 
	108, 109, 110, 111, 114, 115, 117, 120, 
	125, 42, 47, 42, 47, 10, 112, 105, 
	108, 108, 9, 10, 32, 45, 47, 115, 
	115, 108, 111, 116, 115, 9, 10, 32, 
	47, 48, 49, 57, 9, 10, 32, 47, 
	48, 49, 57, 42, 47, 42, 47, 10, 
	9, 10, 32, 47, 59, 120, 48, 55, 
	9, 10, 32, 47, 59, 9, 10, 32, 
	47, 59, 42, 47, 42, 47, 10, 9, 
	10, 32, 47, 59, 48, 55, 48, 57, 
	65, 70, 97, 102, 9, 10, 32, 47, 
	59, 48, 57, 65, 70, 97, 102, 9, 
	10, 32, 47, 59, 48, 57, 42, 47, 
	42, 47, 10, 9, 10, 32, 47, 102, 
	9, 10, 32, 47, 102, 0
};

static const char _as_single_lengths[] = {
	0, 2, 0, 1, 1, 1, 1, 1, 
	1, 1, 1, 6, 6, 7, 5, 5, 
	2, 0, 1, 1, 1, 20, 20, 2, 
	3, 19, 19, 2, 0, 1, 1, 1, 
	1, 1, 5, 5, 5, 2, 0, 1, 
	1, 1, 0, 5, 5, 5, 5, 5, 
	2, 0, 1, 1, 1, 0, 5, 5, 
	5, 5, 5, 2, 0, 1, 1, 1, 
	0, 5, 5, 5, 2, 0, 1, 1, 
	1, 19, 1, 5, 1, 6, 5, 1, 
	1, 1, 1, 1, 1, 1, 1, 1, 
	5, 3, 1, 5, 5, 5, 2, 7, 
	2, 0, 1, 1, 1, 1, 5, 5, 
	5, 2, 0, 1, 1, 1, 0, 5, 
	5, 5, 2, 0, 1, 1, 1, 5, 
	2, 2, 5, 5, 5, 2, 0, 1, 
	1, 1, 0, 1, 6, 6, 7, 2, 
	0, 1, 1, 1, 5, 5, 5, 2, 
	0, 1, 1, 1, 0, 1, 5, 5, 
	2, 0, 1, 1, 1, 6, 5, 0, 
	5, 5, 6, 5, 1, 1, 5, 5, 
	5, 2, 0, 1, 1, 1, 0, 1, 
	5, 5, 2, 0, 1, 1, 1, 0, 
	5, 1, 5, 1, 5, 1, 1, 5, 
	5, 5, 2, 0, 1, 1, 1, 0, 
	5, 1, 1, 1, 1, 5, 5, 5, 
	2, 0, 1, 1, 1, 0, 1, 1, 
	1, 1, 1, 1, 1, 5, 5, 5, 
	2, 0, 1, 1, 1, 0, 1, 5, 
	5, 2, 0, 1, 1, 1, 0, 5, 
	1, 1, 5, 2, 0, 1, 1, 1, 
	2, 0, 1, 1, 1, 2, 0, 1, 
	1, 1, 1, 1, 1, 1, 1, 1, 
	1, 1, 5, 5, 2, 0, 1, 1, 
	1, 7, 7, 7, 5, 5, 2, 0, 
	1, 1, 1, 7, 7, 1, 1, 5, 
	5, 2, 0, 1, 1, 1, 2, 0, 
	1, 1, 1, 6, 5, 0, 5, 5, 
	1, 1, 1, 2, 0, 1, 1, 1, 
	19, 19, 2, 0, 1, 1, 1, 1, 
	1, 1, 1, 6, 1, 1, 1, 1, 
	1, 5, 5, 2, 0, 1, 1, 1, 
	6, 5, 5, 2, 0, 1, 1, 1, 
	5, 0, 5, 5, 2, 0, 1, 1, 
	1, 5, 5
};

static const char _as_range_lengths[] = {
	0, 0, 0, 0, 0, 0, 0, 0, 
	0, 0, 0, 2, 2, 3, 0, 0, 
	0, 0, 0, 0, 0, 0, 0, 2, 
	3, 0, 0, 0, 0, 0, 0, 0, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	0, 0, 1, 1, 0, 0, 0, 0, 
	0, 0, 0, 0, 0, 1, 1, 0, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	1, 1, 0, 0, 0, 0, 0, 0, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	0, 0, 0, 0, 0, 0, 2, 3, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	0, 0, 0, 0, 0, 0, 1, 1, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	0, 0, 1, 1, 2, 2, 3, 0, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	0, 0, 0, 0, 1, 1, 1, 1, 
	0, 0, 0, 0, 0, 1, 1, 3, 
	3, 1, 0, 0, 0, 0, 0, 0, 
	0, 0, 0, 0, 0, 0, 1, 1, 
	0, 0, 0, 0, 0, 0, 0, 1, 
	1, 0, 0, 0, 0, 0, 0, 0, 
	0, 0, 0, 0, 0, 0, 0, 1, 
	1, 0, 0, 0, 0, 0, 0, 0, 
	0, 0, 0, 0, 0, 1, 1, 0, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	0, 0, 0, 0, 0, 1, 1, 0, 
	0, 0, 0, 0, 0, 0, 1, 1, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	0, 2, 2, 3, 0, 0, 0, 0, 
	0, 0, 0, 1, 1, 0, 0, 0, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	0, 0, 0, 1, 1, 3, 3, 1, 
	0, 3, 3, 0, 0, 0, 0, 0, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	0, 1, 1, 0, 0, 0, 0, 0, 
	1, 0, 0, 0, 0, 0, 0, 0, 
	1, 3, 3, 1, 0, 0, 0, 0, 
	0, 0, 0
};

static const short _as_index_offsets[] = {
	0, 0, 3, 4, 6, 8, 10, 12, 
	14, 16, 18, 20, 29, 38, 49, 55, 
	61, 64, 65, 67, 69, 71, 92, 113, 
	118, 125, 145, 165, 168, 169, 171, 173, 
	175, 177, 179, 185, 191, 197, 200, 201, 
	203, 205, 207, 209, 216, 222, 228, 234, 
	240, 243, 244, 246, 248, 250, 252, 259, 
	265, 271, 277, 283, 286, 287, 289, 291, 
	293, 295, 302, 308, 314, 317, 318, 320, 
	322, 324, 344, 346, 352, 354, 361, 367, 
	369, 371, 373, 375, 377, 379, 381, 383, 
	385, 391, 395, 397, 403, 409, 415, 420, 
	431, 434, 435, 437, 439, 441, 443, 449, 
	455, 461, 464, 465, 467, 469, 471, 473, 
	480, 486, 492, 495, 496, 498, 500, 502, 
	508, 511, 514, 520, 526, 532, 535, 536, 
	538, 540, 542, 544, 547, 556, 565, 576, 
	579, 580, 582, 584, 586, 592, 598, 604, 
	607, 608, 610, 612, 614, 616, 619, 626, 
	633, 636, 637, 639, 641, 643, 651, 658, 
	662, 671, 678, 685, 691, 693, 695, 701, 
	707, 713, 716, 717, 719, 721, 723, 725, 
	728, 734, 740, 743, 744, 746, 748, 750, 
	752, 759, 761, 767, 769, 775, 777, 779, 
	785, 791, 797, 800, 801, 803, 805, 807, 
	809, 816, 818, 820, 822, 824, 830, 836, 
	842, 845, 846, 848, 850, 852, 854, 857, 
	859, 861, 863, 865, 867, 869, 875, 881, 
	887, 890, 891, 893, 895, 897, 899, 902, 
	908, 914, 917, 918, 920, 922, 924, 926, 
	933, 935, 937, 943, 946, 947, 949, 951, 
	953, 956, 957, 959, 961, 963, 966, 967, 
	969, 971, 973, 975, 977, 979, 981, 983, 
	985, 987, 989, 995, 1001, 1004, 1005, 1007, 
	1009, 1011, 1021, 1031, 1042, 1048, 1054, 1057, 
	1058, 1060, 1062, 1064, 1073, 1082, 1084, 1086, 
	1092, 1098, 1101, 1102, 1104, 1106, 1108, 1111, 
	1112, 1114, 1116, 1118, 1126, 1133, 1137, 1146, 
	1153, 1155, 1160, 1165, 1168, 1169, 1171, 1173, 
	1175, 1195, 1215, 1218, 1219, 1221, 1223, 1225, 
	1227, 1229, 1231, 1233, 1240, 1242, 1244, 1246, 
	1248, 1250, 1257, 1264, 1267, 1268, 1270, 1272, 
	1274, 1282, 1288, 1294, 1297, 1298, 1300, 1302, 
	1304, 1311, 1315, 1324, 1331, 1334, 1335, 1337, 
	1339, 1341, 1347
};

static const short _as_trans_targs[] = {
	2, 5, 0, 3, 4, 0, 353, 0, 
	354, 5, 7, 0, 8, 0, 9, 0, 
	10, 0, 11, 0, 11, 12, 11, 13, 
	348, 13, 13, 13, 0, 11, 12, 11, 
	13, 348, 13, 13, 13, 0, 14, 15, 
	14, 13, 16, 13, 21, 13, 13, 13, 
	0, 14, 15, 14, 16, 21, 0, 14, 
	15, 14, 16, 21, 0, 17, 20, 0, 
	18, 19, 0, 14, 0, 15, 20, 21, 
	22, 21, 23, 253, 32, 258, 74, 76, 
	79, 89, 120, 164, 185, 187, 189, 319, 
	215, 240, 353, 0, 21, 22, 21, 23, 
	253, 32, 258, 74, 76, 79, 89, 120, 
	164, 185, 187, 189, 319, 215, 240, 353, 
	0, 24, 24, 24, 24, 0, 24, 25, 
	24, 24, 24, 24, 0, 25, 26, 25, 
	23, 27, 32, 74, 76, 79, 89, 120, 
	164, 185, 187, 189, 201, 215, 240, 353, 
	0, 25, 26, 25, 23, 27, 32, 74, 
	76, 79, 89, 120, 164, 185, 187, 189, 
	201, 215, 240, 353, 0, 28, 31, 0, 
	29, 30, 0, 25, 0, 26, 31, 33, 
	0, 34, 0, 35, 36, 35, 37, 42, 
	0, 35, 36, 35, 37, 42, 0, 35, 
	36, 35, 37, 42, 0, 38, 41, 0, 
	39, 40, 0, 35, 0, 36, 41, 43, 
	0, 44, 45, 44, 46, 248, 43, 0, 
	44, 45, 44, 46, 248, 0, 44, 45, 
	44, 46, 248, 0, 46, 47, 46, 48, 
	53, 0, 46, 47, 46, 48, 53, 0, 
	49, 52, 0, 50, 51, 0, 46, 0, 
	47, 52, 54, 0, 55, 56, 55, 57, 
	243, 54, 0, 55, 56, 55, 57, 243, 
	0, 55, 56, 55, 57, 243, 0, 57, 
	58, 57, 59, 64, 0, 57, 58, 57, 
	59, 64, 0, 60, 63, 0, 61, 62, 
	0, 57, 0, 58, 63, 65, 0, 66, 
	67, 66, 68, 73, 65, 0, 66, 67, 
	66, 68, 73, 0, 66, 67, 66, 68, 
	73, 0, 69, 72, 0, 70, 71, 0, 
	66, 0, 67, 72, 25, 26, 25, 23, 
	27, 32, 74, 76, 79, 89, 120, 164, 
	185, 187, 189, 201, 215, 240, 353, 0, 
	75, 0, 35, 36, 35, 37, 42, 0, 
	77, 0, 35, 36, 35, 37, 78, 42, 
	0, 35, 36, 35, 37, 42, 0, 80, 
	0, 81, 0, 82, 0, 83, 0, 84, 
	0, 85, 0, 86, 0, 87, 0, 88, 
	0, 35, 36, 35, 37, 42, 0, 90, 
	101, 119, 0, 91, 0, 92, 93, 92, 
	94, 96, 0, 92, 93, 92, 94, 96, 
	0, 92, 93, 92, 94, 96, 0, 95, 
	95, 95, 95, 0, 66, 67, 66, 95, 
	68, 73, 95, 95, 95, 95, 0, 97, 
	100, 0, 98, 99, 0, 92, 0, 93, 
	100, 102, 0, 103, 104, 103, 105, 110, 
	0, 103, 104, 103, 105, 110, 0, 103, 
	104, 103, 105, 110, 0, 106, 109, 0, 
	107, 108, 0, 103, 0, 104, 109, 111, 
	0, 112, 113, 112, 92, 114, 111, 0, 
	112, 113, 112, 92, 114, 0, 112, 113, 
	112, 92, 114, 0, 115, 118, 0, 116, 
	117, 0, 112, 0, 113, 118, 103, 104, 
	103, 105, 110, 0, 121, 162, 0, 122, 
	140, 0, 123, 124, 123, 125, 130, 0, 
	123, 124, 123, 125, 130, 0, 123, 124, 
	123, 125, 130, 0, 126, 129, 0, 127, 
	128, 0, 123, 0, 124, 129, 131, 0, 
	132, 131, 0, 132, 133, 132, 134, 135, 
	134, 134, 134, 0, 132, 133, 132, 134, 
	135, 134, 134, 134, 0, 66, 67, 66, 
	134, 68, 73, 134, 134, 134, 134, 0, 
	136, 139, 0, 137, 138, 0, 132, 0, 
	133, 139, 141, 142, 141, 143, 148, 0, 
	141, 142, 141, 143, 148, 0, 141, 142, 
	141, 143, 148, 0, 144, 147, 0, 145, 
	146, 0, 141, 0, 142, 147, 149, 0, 
	150, 149, 0, 150, 151, 150, 152, 157, 
	161, 0, 150, 151, 150, 152, 157, 161, 
	0, 153, 156, 0, 154, 155, 0, 150, 
	0, 151, 156, 66, 67, 66, 68, 73, 
	159, 158, 0, 66, 67, 66, 68, 73, 
	158, 0, 160, 160, 160, 0, 66, 67, 
	66, 68, 73, 160, 160, 160, 0, 66, 
	67, 66, 68, 73, 161, 0, 35, 36, 
	35, 37, 163, 42, 0, 35, 36, 35, 
	37, 42, 0, 165, 0, 166, 0, 167, 
	168, 167, 169, 174, 0, 167, 168, 167, 
	169, 174, 0, 167, 168, 167, 169, 174, 
	0, 170, 173, 0, 171, 172, 0, 167, 
	0, 168, 173, 175, 0, 176, 175, 0, 
	176, 177, 176, 178, 183, 0, 176, 177, 
	176, 178, 183, 0, 179, 182, 0, 180, 
	181, 0, 176, 0, 177, 182, 184, 0, 
	66, 67, 66, 68, 73, 184, 0, 186, 
	0, 35, 36, 35, 37, 42, 0, 188, 
	0, 35, 36, 35, 37, 42, 0, 190, 
	0, 191, 0, 192, 193, 192, 194, 199, 
	0, 192, 193, 192, 194, 199, 0, 192, 
	193, 192, 194, 199, 0, 195, 198, 0, 
	196, 197, 0, 192, 0, 193, 198, 200, 
	0, 66, 67, 66, 68, 73, 200, 0, 
	202, 0, 203, 0, 204, 0, 205, 0, 
	206, 207, 206, 208, 213, 0, 206, 207, 
	206, 208, 213, 0, 206, 207, 206, 208, 
	213, 0, 209, 212, 0, 210, 211, 0, 
	206, 0, 207, 212, 214, 0, 57, 214, 
	0, 216, 0, 217, 0, 218, 0, 219, 
	0, 220, 0, 221, 0, 222, 223, 222, 
	224, 229, 0, 222, 223, 222, 224, 229, 
	0, 222, 223, 222, 224, 229, 0, 225, 
	228, 0, 226, 227, 0, 222, 0, 223, 
	228, 230, 0, 231, 230, 0, 231, 232, 
	231, 233, 238, 0, 231, 232, 231, 233, 
	238, 0, 234, 237, 0, 235, 236, 0, 
	231, 0, 232, 237, 239, 0, 66, 67, 
	66, 68, 73, 239, 0, 241, 0, 242, 
	0, 35, 36, 35, 37, 42, 0, 244, 
	247, 0, 245, 246, 0, 55, 0, 56, 
	247, 249, 252, 0, 250, 251, 0, 44, 
	0, 45, 252, 254, 257, 0, 255, 256, 
	0, 21, 0, 22, 257, 259, 0, 260, 
	0, 261, 0, 262, 0, 263, 0, 264, 
	0, 265, 0, 266, 0, 266, 267, 266, 
	268, 273, 0, 266, 267, 266, 268, 273, 
	0, 269, 272, 0, 270, 271, 0, 266, 
	0, 267, 272, 273, 274, 273, 275, 307, 
	275, 312, 275, 275, 0, 273, 274, 273, 
	275, 307, 275, 312, 275, 275, 0, 276, 
	277, 276, 275, 278, 283, 275, 275, 275, 
	275, 0, 276, 277, 276, 278, 283, 0, 
	276, 277, 276, 278, 283, 0, 279, 282, 
	0, 280, 281, 0, 276, 0, 277, 282, 
	283, 284, 283, 285, 294, 299, 304, 303, 
	0, 283, 284, 283, 285, 294, 299, 304, 
	303, 0, 287, 286, 287, 286, 287, 288, 
	287, 289, 273, 0, 287, 288, 287, 289, 
	273, 0, 290, 293, 0, 291, 292, 0, 
	287, 0, 288, 293, 295, 298, 0, 296, 
	297, 0, 283, 0, 284, 298, 287, 288, 
	287, 289, 273, 301, 300, 0, 287, 288, 
	287, 289, 273, 300, 0, 302, 302, 302, 
	0, 287, 288, 287, 289, 273, 302, 302, 
	302, 0, 287, 288, 287, 289, 273, 303, 
	0, 305, 0, 287, 306, 306, 306, 0, 
	287, 306, 306, 306, 0, 308, 311, 0, 
	309, 310, 0, 273, 0, 274, 311, 312, 
	313, 312, 23, 314, 32, 74, 76, 79, 
	89, 120, 164, 185, 187, 189, 319, 215, 
	240, 353, 0, 312, 313, 312, 23, 314, 
	32, 74, 76, 79, 89, 120, 164, 185, 
	187, 189, 319, 215, 240, 353, 0, 315, 
	318, 0, 316, 317, 0, 312, 0, 313, 
	318, 320, 0, 321, 0, 322, 0, 323, 
	0, 206, 207, 206, 324, 208, 213, 0, 
	325, 0, 326, 0, 327, 0, 328, 0, 
	329, 0, 329, 330, 329, 331, 336, 347, 
	0, 329, 330, 329, 331, 336, 347, 0, 
	332, 335, 0, 333, 334, 0, 329, 0, 
	330, 335, 337, 338, 337, 339, 25, 345, 
	344, 0, 337, 338, 337, 339, 25, 0, 
	337, 338, 337, 339, 25, 0, 340, 343, 
	0, 341, 342, 0, 337, 0, 338, 343, 
	337, 338, 337, 339, 25, 344, 0, 346, 
	346, 346, 0, 337, 338, 337, 339, 25, 
	346, 346, 346, 0, 337, 338, 337, 339, 
	25, 347, 0, 349, 352, 0, 350, 351, 
	0, 11, 0, 12, 352, 353, 354, 353, 
	1, 6, 0, 353, 354, 353, 1, 6, 
	0, 0
};

static const unsigned char _as_trans_actions[] = {
	0, 0, 0, 0, 0, 0, 0, 0, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	0, 0, 0, 0, 0, 0, 0, 3, 
	0, 3, 3, 3, 0, 1, 1, 1, 
	77, 1, 77, 77, 77, 0, 5, 5, 
	5, 0, 5, 0, 5, 0, 0, 0, 
	0, 0, 0, 0, 0, 0, 0, 1, 
	1, 1, 1, 1, 0, 0, 0, 0, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	0, 0, 7, 0, 1, 1, 1, 1, 
	1, 1, 1, 1, 1, 1, 1, 1, 
	1, 1, 1, 1, 1, 1, 1, 80, 
	0, 3, 3, 3, 3, 0, 0, 75, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	0, 0, 0, 0, 0, 0, 0, 7, 
	0, 1, 1, 1, 1, 1, 1, 1, 
	1, 1, 1, 1, 1, 1, 1, 1, 
	1, 1, 1, 80, 0, 0, 0, 0, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	0, 0, 0, 43, 43, 43, 43, 107, 
	0, 0, 0, 0, 0, 3, 0, 1, 
	1, 1, 1, 77, 0, 0, 0, 0, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	0, 19, 19, 19, 19, 19, 0, 0, 
	0, 0, 0, 0, 0, 0, 1, 1, 
	1, 1, 1, 0, 0, 0, 0, 0, 
	3, 0, 1, 1, 1, 1, 77, 0, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	0, 0, 0, 0, 21, 21, 21, 21, 
	21, 0, 0, 0, 0, 0, 0, 0, 
	0, 1, 1, 1, 1, 1, 0, 0, 
	0, 0, 0, 3, 0, 1, 1, 1, 
	1, 77, 0, 0, 0, 0, 0, 0, 
	0, 0, 0, 0, 0, 0, 0, 23, 
	23, 23, 23, 23, 0, 0, 0, 0, 
	0, 0, 0, 0, 1, 1, 1, 1, 
	1, 0, 0, 0, 0, 0, 0, 0, 
	0, 0, 0, 0, 31, 31, 31, 31, 
	31, 31, 31, 31, 31, 31, 31, 31, 
	31, 31, 31, 31, 31, 31, 89, 0, 
	0, 0, 49, 49, 49, 49, 116, 0, 
	0, 0, 53, 53, 53, 53, 0, 122, 
	0, 57, 57, 57, 57, 128, 0, 0, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	0, 61, 61, 61, 61, 134, 0, 0, 
	0, 0, 0, 0, 0, 69, 69, 69, 
	69, 69, 0, 0, 0, 0, 0, 0, 
	0, 1, 1, 1, 1, 1, 0, 3, 
	3, 3, 3, 0, 67, 67, 67, 0, 
	67, 67, 0, 0, 0, 0, 0, 0, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	0, 0, 0, 71, 71, 71, 71, 140, 
	0, 0, 0, 0, 0, 3, 0, 1, 
	1, 1, 1, 77, 0, 0, 0, 0, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	0, 19, 19, 19, 19, 19, 0, 0, 
	0, 0, 0, 0, 0, 0, 1, 1, 
	1, 1, 1, 0, 0, 0, 0, 0, 
	0, 0, 0, 0, 0, 0, 73, 73, 
	73, 73, 143, 0, 0, 0, 0, 0, 
	0, 0, 65, 65, 65, 65, 137, 0, 
	0, 0, 0, 0, 3, 0, 1, 1, 
	1, 1, 77, 0, 0, 0, 0, 0, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	19, 0, 0, 0, 0, 0, 3, 0, 
	3, 3, 3, 0, 1, 1, 1, 77, 
	1, 77, 77, 77, 0, 63, 63, 63, 
	0, 63, 63, 0, 0, 0, 0, 0, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	0, 0, 39, 39, 39, 39, 101, 0, 
	0, 0, 0, 0, 3, 0, 1, 1, 
	1, 1, 77, 0, 0, 0, 0, 0, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	19, 0, 0, 0, 0, 0, 0, 3, 
	3, 0, 1, 1, 1, 1, 77, 77, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	0, 0, 0, 29, 29, 29, 29, 29, 
	0, 0, 0, 29, 29, 29, 29, 29, 
	0, 0, 0, 0, 0, 0, 29, 29, 
	29, 29, 29, 0, 0, 0, 0, 29, 
	29, 29, 29, 29, 0, 0, 55, 55, 
	55, 55, 0, 125, 0, 59, 59, 59, 
	59, 131, 0, 0, 0, 0, 0, 33, 
	33, 33, 33, 92, 0, 0, 0, 0, 
	0, 3, 0, 1, 1, 1, 1, 77, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	0, 0, 0, 0, 0, 19, 0, 0, 
	0, 0, 0, 0, 3, 0, 1, 1, 
	1, 1, 77, 0, 0, 0, 0, 0, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	21, 21, 21, 21, 21, 0, 0, 0, 
	0, 51, 51, 51, 51, 119, 0, 0, 
	0, 45, 45, 45, 45, 110, 0, 0, 
	0, 0, 0, 41, 41, 41, 41, 104, 
	0, 0, 0, 0, 0, 3, 0, 1, 
	1, 1, 1, 77, 0, 0, 0, 0, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	0, 19, 19, 19, 19, 19, 0, 0, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	35, 35, 35, 35, 95, 0, 0, 0, 
	0, 0, 3, 0, 1, 1, 1, 1, 
	77, 0, 0, 0, 0, 0, 0, 0, 
	0, 0, 0, 0, 0, 0, 25, 0, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	0, 0, 0, 0, 0, 37, 37, 37, 
	37, 98, 0, 0, 0, 0, 0, 3, 
	0, 1, 1, 1, 1, 77, 0, 0, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	0, 0, 0, 19, 0, 0, 0, 0, 
	0, 0, 3, 0, 1, 1, 1, 1, 
	77, 0, 0, 0, 0, 0, 0, 0, 
	0, 0, 0, 0, 0, 0, 27, 27, 
	27, 27, 27, 0, 0, 0, 0, 0, 
	0, 47, 47, 47, 47, 113, 0, 0, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	0, 0, 0, 1, 1, 1, 1, 1, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	0, 0, 0, 0, 0, 0, 3, 0, 
	3, 0, 3, 3, 0, 1, 1, 1, 
	77, 1, 77, 1, 77, 77, 0, 9, 
	9, 9, 0, 9, 9, 0, 0, 0, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	1, 1, 1, 1, 1, 0, 0, 0, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	0, 0, 0, 0, 0, 3, 0, 3, 
	0, 1, 1, 1, 1, 1, 77, 1, 
	77, 0, 86, 3, 13, 0, 0, 0, 
	0, 0, 0, 0, 1, 1, 1, 1, 
	1, 0, 0, 0, 0, 0, 0, 0, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	0, 0, 0, 0, 0, 0, 15, 15, 
	15, 15, 15, 0, 0, 0, 15, 15, 
	15, 15, 15, 0, 0, 0, 0, 0, 
	0, 15, 15, 15, 15, 15, 0, 0, 
	0, 0, 15, 15, 15, 15, 15, 0, 
	0, 0, 0, 83, 3, 3, 3, 0, 
	11, 0, 0, 0, 0, 0, 0, 0, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	0, 7, 0, 1, 1, 1, 1, 1, 
	1, 1, 1, 1, 1, 1, 1, 1, 
	1, 1, 1, 1, 1, 80, 0, 0, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	0, 35, 35, 35, 0, 35, 95, 0, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	0, 0, 0, 0, 0, 0, 3, 3, 
	0, 1, 1, 1, 1, 77, 77, 0, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	0, 0, 17, 17, 17, 17, 17, 0, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	1, 1, 1, 1, 1, 0, 0, 0, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	17, 17, 17, 17, 17, 0, 0, 0, 
	0, 0, 0, 17, 17, 17, 17, 17, 
	0, 0, 0, 0, 17, 17, 17, 17, 
	17, 0, 0, 0, 0, 0, 0, 0, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	0, 0, 0, 1, 1, 1, 1, 1, 
	0, 0
};

static const unsigned char _as_eof_actions[] = {
	0, 0, 0, 0, 0, 0, 0, 0, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	0, 0, 0, 0, 0, 0, 0, 0, 
	0, 0, 1
};

static const int as_start = 353;
static const int as_first_final = 353;
static const int as_error = 0;

static const int as_en_as = 353;


#line 910 "lsmsb-as.rl"


struct Constant {
  explicit Constant(const std::string &n)
      : name(n), gap(0), small(false), used(false) {
  }

  enum Type {
    TYPE_U32,
    TYPE_BYTESTRING,
  };

  const std::string name;
  unsigned gap;
  bool small;
  bool used;

  virtual Type type() const = 0;
  virtual bool Write() const = 0;
};

struct ByteString : public Constant {
  ByteString(const std::string &name, const std::string &ivalue)
      : Constant(name),
        value(ivalue) {
  }

  Type type() const {
    return TYPE_BYTESTRING;
  }

  bool Write() const {
    struct lsmsb_constant_wire wire;

    wire.type = TYPE_BYTESTRING;
    wire.value = value.size();

    if (!writea(1, &wire, sizeof(wire)) ||
        !writea(1, value.data(), value.size())) {
      return false;
    }

    return true;
  }

  const std::string value;
};

struct U32 : public Constant {
  U32(const std::string &name, uint32_t v)
      : Constant(name),
        value(v) {
    small = ((v & 0xfffff) == v);
  }

  Type type() const {
    return TYPE_U32;
  }

  bool Write() const {
    struct lsmsb_constant_wire wire;

    wire.type = TYPE_U32;
    wire.value = value;

    if (!writea(1, &wire, sizeof(wire)))
      return false;

    return true;
  }

  const uint32_t value;
};
struct Filter {
  Filter()
      : spill_slots(0),
        type_string(NULL),
        filter_code(LSMSB_FILTER_CODE_MAX) {
  }

  bool Typecheck() const {
    const unsigned data_len = sizeof(struct lsmsb_filter) +
                              constants.size() * sizeof(struct lsmsb_value);
    uint8_t *filter_data = reinterpret_cast<uint8_t*>(malloc(data_len));
    memset(filter_data, 0, data_len);
    struct lsmsb_filter *filter = reinterpret_cast<lsmsb_filter*>(filter_data);

    filter->num_operations = ops.size();
    filter->num_spill_slots = spill_slots;
    filter->num_constants = constants.size();
    filter->operations = const_cast<uint32_t*>(&ops[0]);
    for (unsigned i = 0; i < constants.size(); ++i) {
      // It doesn't matter what value we use, as long as it isn't NULL so
      // |filter_data| is as good as any.
      filter->constants[i].data = constants[i]->type() == Constant::TYPE_BYTESTRING ?
                                  filter_data : NULL;
    }

    uint8_t* type_vector = type_vector_for_filter(filter, type_string);

    const bool ret = lsmsb_filter_typecheck(filter, type_vector);
    free(type_vector);
    free(filter);

    return ret;
  }
  unsigned OptimizeConstants() {
    unsigned i, j, k = 0;
    for (i = 0; i < constants.size(); ++i) {
      if (constants[i]->small) {
        constants[i]->used = false;
      }
      if (!constants[i]->used) {
        k++;
      } else {
        constants[i]->gap = k;
      }
    }
    for (j = 0; j < ops.size(); ++j) {
      uint32_t op = ops[j];
      if (lsmsb_op_opcode_get(op) == LSMSB_OPCODE_LDC) {
        unsigned gap, c1 = lsmsb_op_constant1_get(op);
        if (!constants[c1]->used) {
          // We get here because the used flag was cleared above.  It means the
          // constant value is small enough to fit into an immediate.  We could
          // have done this early, in set_const, and leave the constant unused.
          uint32_t imm = ((U32 *)constants[c1])->value;
          op &= ~0xFF0FFFFF;
          op |= (static_cast<uint32_t>(LSMSB_OPCODE_LDI) << 24) | imm;
          ops[j] = op;
          continue;
        }
        gap = constants[c1]->gap;
        if (gap) {
          op &= ~0xFF;
          op |= c1 - gap;
          ops[j] = op;
        }
      }
    }
    return k;
  }
  bool Write(bool optimize = true) {
    struct lsmsb_filter_wire wire;
    wire.filter_code = filter_code;
    wire.num_operations = ops.size();
    wire.num_spill_slots = spill_slots;
    wire.num_constants = constants.size();
    if (optimize)
      wire.num_constants -= OptimizeConstants();

    if (!writea(1, &wire, sizeof(wire)) ||
        !writea(1, &ops[0], sizeof(uint32_t) * ops.size())) {
      return false;
    }

    for (std::vector<Constant*>::const_iterator
         i = constants.begin(); i != constants.end(); ++i) {
      if (optimize && !(*i)->used)
        continue;
      if (!(*i)->Write())
        return false;
    }

    return true;
  }

  std::string name;  // the name of the filter (i.e. "dentry-open")
  std::vector<Constant*> constants;
  unsigned spill_slots;
  std::vector<uint32_t> ops;
  const char *type_string;  // the types of this filter's context
  unsigned filter_code;  // the enum value of the filter
};
int
main(int argc, char **argv) {
  if (argc != 2) {
    fprintf(stderr, "Usage: %s <input file>\n", argv[0]);
    return 1;
  }

  const int fd = open(argv[1], O_RDONLY);
  if (fd < 0) {
    perror("Cannot open input file");
    return 1;
  }

  struct stat st;
  fstat(fd, &st);

  char *input = (char *) malloc(st.st_size);
  read(fd, input, st.st_size);
  close(fd);

  int cs;  // current parsing state
  uint32_t op = 0;  // current operation
  char *p = input;  // pointer to input
  const char *start = NULL;
  char *const pe = input + st.st_size;
  char *const eof = pe;
  unsigned line_no = 1;
  std::map<std::string, std::vector<unsigned> > jmp_targets;
  std::vector<Filter*> filters;
  Filter *current_filter = NULL;
  std::string current_const_name;

  
#line 1605 "lsmsb-as.cc"
	{
	cs = as_start;
	}

#line 1117 "lsmsb-as.rl"
  
#line 1612 "lsmsb-as.cc"
	{
	int _klen;
	unsigned int _trans;
	const char *_acts;
	unsigned int _nacts;
	const char *_keys;

	if ( p == pe )
		goto _test_eof;
	if ( cs == 0 )
		goto _out;
_resume:
	_keys = _as_trans_keys + _as_key_offsets[cs];
	_trans = _as_index_offsets[cs];

	_klen = _as_single_lengths[cs];
	if ( _klen > 0 ) {
		const char *_lower = _keys;
		const char *_mid;
		const char *_upper = _keys + _klen - 1;
		while (1) {
			if ( _upper < _lower )
				break;

			_mid = _lower + ((_upper-_lower) >> 1);
			if ( (*p) < *_mid )
				_upper = _mid - 1;
			else if ( (*p) > *_mid )
				_lower = _mid + 1;
			else {
				_trans += (_mid - _keys);
				goto _match;
			}
		}
		_keys += _klen;
		_trans += _klen;
	}

	_klen = _as_range_lengths[cs];
	if ( _klen > 0 ) {
		const char *_lower = _keys;
		const char *_mid;
		const char *_upper = _keys + (_klen<<1) - 2;
		while (1) {
			if ( _upper < _lower )
				break;

			_mid = _lower + (((_upper-_lower) >> 1) & ~1);
			if ( (*p) < _mid[0] )
				_upper = _mid - 2;
			else if ( (*p) > _mid[1] )
				_lower = _mid + 2;
			else {
				_trans += ((_mid - _keys)>>1);
				goto _match;
			}
		}
		_trans += _klen;
	}

_match:
	cs = _as_trans_targs[_trans];

	if ( _as_trans_actions[_trans] == 0 )
		goto _again;

	_acts = _as_actions + _as_trans_actions[_trans];
	_nacts = (unsigned int) *_acts++;
	while ( _nacts-- > 0 )
	{
		switch ( *_acts++ )
		{
	case 0:
#line 640 "lsmsb-as.rl"
	{
    line_no++;
  }
	break;
	case 1:
#line 646 "lsmsb-as.rl"
	{
    start = p;
  }
	break;
	case 2:
#line 650 "lsmsb-as.rl"
	{
    current_filter = new Filter;
    current_filter->name = std::string(start, p - start);

    for (unsigned i = 0; ; ++i) {
      if (filter_contexts[i].filter_name == NULL) {
        fprintf(stderr, "Error line %u: Unknown filter name '%s'\n", line_no, current_filter->name.c_str());
        abort();
      }

      if (filter_contexts[i].filter_name == current_filter->name) {
        current_filter->filter_code = i;
        current_filter->type_string = filter_contexts[i].type_string;
        break;
      }
    }
  }
	break;
	case 3:
#line 668 "lsmsb-as.rl"
	{
    filters.push_back(current_filter);
    current_filter = NULL;
    jmp_targets.clear();
  }
	break;
	case 4:
#line 674 "lsmsb-as.rl"
	{
    current_const_name = std::string(start, p - start);
  }
	break;
	case 5:
#line 678 "lsmsb-as.rl"
	{
    current_filter->constants.push_back(new ByteString(current_const_name, hex_parse(std::string(start, p - start))));
  }
	break;
	case 6:
#line 682 "lsmsb-as.rl"
	{
    current_filter->constants.push_back(new ByteString(current_const_name, std::string(start, p - start)));
  }
	break;
	case 7:
#line 686 "lsmsb-as.rl"
	{
    current_filter->constants.push_back(new U32(current_const_name, u32_parse(std::string(start, p - start))));
  }
	break;
	case 8:
#line 699 "lsmsb-as.rl"
	{
    current_filter->spill_slots = u32_parse(std::string(start, p - start));
    if (current_filter->spill_slots > LSMSB_SPILL_SLOTS_MAX) {
      fprintf(stderr, "Error line %u: Invalid number of spill slots: %d\n", line_no, current_filter->spill_slots);
      abort();
    }
  }
	break;
	case 9:
#line 712 "lsmsb-as.rl"
	{
    op |= reg_parse(std::string(start, p - start), LSMSB_NUM_REGISTERS) << 20;
  }
	break;
	case 10:
#line 715 "lsmsb-as.rl"
	{
    op |= reg_parse(std::string(start, p - start), LSMSB_NUM_REGISTERS) << 16;
  }
	break;
	case 11:
#line 718 "lsmsb-as.rl"
	{
    op |= reg_parse(std::string(start, p - start), LSMSB_NUM_REGISTERS) << 12;
  }
	break;
	case 12:
#line 721 "lsmsb-as.rl"
	{
    op |= reg_parse(std::string(start, p - start), current_filter->spill_slots) << 16;
  }
	break;
	case 13:
#line 724 "lsmsb-as.rl"
	{
    op |= reg_parse(std::string(start, p - start), current_filter->spill_slots) << 12;
  }
	break;
	case 14:
#line 727 "lsmsb-as.rl"
	{
    op |= imm_check(u32_parse(std::string(start, p - start)));
  }
	break;
	case 15:
#line 730 "lsmsb-as.rl"
	{
    current_filter->ops.push_back(op);
    op = 0;
  }
	break;
	case 16:
#line 734 "lsmsb-as.rl"
	{
    op |= static_cast<uint32_t>(LSMSB_OPCODE_MOV) << 24;
  }
	break;
	case 17:
#line 739 "lsmsb-as.rl"
	{
    op |= static_cast<uint32_t>(LSMSB_OPCODE_SPILL) << 24;
  }
	break;
	case 18:
#line 744 "lsmsb-as.rl"
	{
    op |= static_cast<uint32_t>(LSMSB_OPCODE_UNSPILL) << 24;
  }
	break;
	case 19:
#line 749 "lsmsb-as.rl"
	{
    op |= static_cast<uint32_t>(LSMSB_OPCODE_LDI) << 24;
  }
	break;
	case 20:
#line 754 "lsmsb-as.rl"
	{
    op |= static_cast<uint32_t>(LSMSB_OPCODE_RET) << 24;
  }
	break;
	case 21:
#line 764 "lsmsb-as.rl"
	{
    op |= static_cast<uint32_t>(LSMSB_OPCODE_AND) << 24;
  }
	break;
	case 22:
#line 771 "lsmsb-as.rl"
	{
    op |= static_cast<uint32_t>(LSMSB_OPCODE_OR) << 24;
  }
	break;
	case 23:
#line 778 "lsmsb-as.rl"
	{
    op |= static_cast<uint32_t>(LSMSB_OPCODE_XOR) << 24;
  }
	break;
	case 24:
#line 785 "lsmsb-as.rl"
	{
    op |= static_cast<uint32_t>(LSMSB_OPCODE_EQ) << 24;
  }
	break;
	case 25:
#line 792 "lsmsb-as.rl"
	{
    op |= static_cast<uint32_t>(LSMSB_OPCODE_NE) << 24;
  }
	break;
	case 26:
#line 799 "lsmsb-as.rl"
	{
    op |= static_cast<uint32_t>(LSMSB_OPCODE_GT) << 24;
  }
	break;
	case 27:
#line 806 "lsmsb-as.rl"
	{
    op |= static_cast<uint32_t>(LSMSB_OPCODE_LT) << 24;
  }
	break;
	case 28:
#line 813 "lsmsb-as.rl"
	{
    op |= static_cast<uint32_t>(LSMSB_OPCODE_GTE) << 24;
  }
	break;
	case 29:
#line 820 "lsmsb-as.rl"
	{
    op |= static_cast<uint32_t>(LSMSB_OPCODE_LTE) << 24;
  }
	break;
	case 30:
#line 827 "lsmsb-as.rl"
	{
    op |= static_cast<uint32_t>(LSMSB_OPCODE_ISPREFIXOF) << 24;
  }
	break;
	case 31:
#line 834 "lsmsb-as.rl"
	{
    const std::string constant_name(start, p - start);
    unsigned i;

    for (i = 0; i < current_filter->constants.size(); ++i) {
      if (current_filter->constants[i]->name == constant_name) {
        current_filter->constants[i]->used = true;
        op |= i;
        break;
      }
    }

    if (i == current_filter->constants.size()) {
      fprintf(stderr, "Error line %u: Unknown constant: %s\n", line_no, constant_name.c_str());
      abort();
    }
  }
	break;
	case 32:
#line 852 "lsmsb-as.rl"
	{
    op |= static_cast<uint32_t>(LSMSB_OPCODE_LDC) << 24;
  }
	break;
	case 33:
#line 857 "lsmsb-as.rl"
	{
    const std::string target = std::string(start, p - start);
    const std::map<std::string, std::vector<unsigned> >::iterator i =
      jmp_targets.find(target);

    if (i == jmp_targets.end()) {
      jmp_targets[target].push_back(current_filter->ops.size());
    } else {
      i->second.push_back(current_filter->ops.size());
    }
  }
	break;
	case 34:
#line 869 "lsmsb-as.rl"
	{
    op |= static_cast<uint32_t>(LSMSB_OPCODE_JMP) << 24;
  }
	break;
	case 35:
#line 874 "lsmsb-as.rl"
	{
    op |= static_cast<uint32_t>(LSMSB_OPCODE_JNZ) << 24;
  }
	break;
	case 36:
#line 879 "lsmsb-as.rl"
	{
    op |= static_cast<uint32_t>(LSMSB_OPCODE_JZ) << 24;
  }
	break;
	case 37:
#line 884 "lsmsb-as.rl"
	{
    const std::string target = std::string(start, p - start);
    const std::map<std::string, std::vector<unsigned> >::iterator i =
      jmp_targets.find(target);

    if (i == jmp_targets.end()) {
      fprintf(stderr, "Error line %u: Jump target without any jumps (%s)\n", line_no, target.c_str());
      abort();
    }

    for (std::vector<unsigned>::const_iterator
         j = i->second.begin(); j != i->second.end(); ++j) {
      current_filter->ops[*j] |= current_filter->ops.size() - *j;
    }

    jmp_targets.erase(i);
  }
	break;
#line 1970 "lsmsb-as.cc"
		}
	}

_again:
	if ( cs == 0 )
		goto _out;
	if ( ++p != pe )
		goto _resume;
	_test_eof: {}
	if ( p == eof )
	{
	const char *__acts = _as_actions + _as_eof_actions[cs];
	unsigned int __nacts = (unsigned int) *__acts++;
	while ( __nacts-- > 0 ) {
		switch ( *__acts++ ) {
	case 0:
#line 640 "lsmsb-as.rl"
	{
    line_no++;
  }
	break;
#line 1992 "lsmsb-as.cc"
		}
	}
	}

	_out: {}
	}

#line 1118 "lsmsb-as.rl"

  if (cs == as_error) {
    fprintf(stderr, "Error line %u: parse failure around: %s\n", line_no, p);
  }

  bool filter_failed = false;
  for (std::vector<Filter*>::const_iterator
       i = filters.begin(); i != filters.end(); ++i) {
    if ((*i)->Typecheck()) {
      fprintf(stderr, "Filter %s failed typecheck.\n", (*i)->name.c_str());
      filter_failed = true;
    }
  }

  if (filter_failed)
    return 1;

  const uint32_t num_filters = filters.size();
  writea(1, &num_filters, sizeof(num_filters));

  for (std::vector<Filter*>::const_iterator
       i = filters.begin(); i != filters.end(); ++i) {
    if (!(*i)->Write()) {
      fprintf(stderr, "Write failure writing to stdout\n");
      abort();
    }
  }

  return 0;
}
