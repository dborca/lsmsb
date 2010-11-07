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

%%{
  machine as;

  action next_line {
    line_no++;
  }

  ws = (' ' | '\t' | ('\n' %next_line) | "//" . (any - '\n')* . ('\n' %next_line) | "/*" . any :>> "*/")*;

  action start {
    start = fpc;
  }

  action filter_new {
    current_filter = new Filter;
    current_filter->name = std::string(start, fpc - start);

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

  action filter_push {
    filters.push_back(current_filter);
    current_filter = NULL;
    jmp_targets.clear();
  }

  action constant_new {
    current_const_name = std::string(start, fpc - start);
  }

  action constant_bytestring_hex {
    current_filter->constants.push_back(new ByteString(current_const_name, hex_parse(std::string(start, fpc - start))));
  }

  action constant_bytestring_string {
    current_filter->constants.push_back(new ByteString(current_const_name, std::string(start, fpc - start)));
  }

  action constant_u32 {
    current_filter->constants.push_back(new U32(current_const_name, u32_parse(std::string(start, fpc - start))));
  }

  token = [a-zA-Z\-_][0-9a-zA-Z\-_]*;
  u32 = ("0x" . xdigit+) | ("0" . [0-7]*) | ([1-9]digit*);
  constant_u32 = (u32 >start %constant_u32);
  bytestring_literal_hex = "x\"" . (xdigit* >start %constant_bytestring_hex) . "\"";
  bytestring_literal_string = "\"" . ((any - '"')* >start %constant_bytestring_string) . "\"";
  constant_bytestring = bytestring_literal_hex | bytestring_literal_string;
  constant = (token >start %constant_new) . ws . "=" . ws . (constant_u32 | constant_bytestring) . ws . ";" . ws;
  constants = "constants" . ws . "{" . ws . constant* . "}" . ws;

  action set_spill_slots {
    current_filter->spill_slots = u32_parse(std::string(start, fpc - start));
    if (current_filter->spill_slots > LSMSB_SPILL_SLOTS_MAX) {
      fprintf(stderr, "Error line %u: Invalid number of spill slots: %d\n", line_no, current_filter->spill_slots);
      abort();
    }
  }

  spillslots = "spill-slots" . ws . (u32 >start %set_spill_slots) . ws . ";" . ws;

  reg = "r" digit+;
  slot = "s" digit+;

  action set_reg1 {
    op |= reg_parse(std::string(start, fpc - start), LSMSB_NUM_REGISTERS) << 20;
  }
  action set_reg2 {
    op |= reg_parse(std::string(start, fpc - start), LSMSB_NUM_REGISTERS) << 16;
  }
  action set_reg3 {
    op |= reg_parse(std::string(start, fpc - start), LSMSB_NUM_REGISTERS) << 12;
  }
  action set_spill1 {
    op |= reg_parse(std::string(start, fpc - start), current_filter->spill_slots) << 16;
  }
  action set_spill2 {
    op |= reg_parse(std::string(start, fpc - start), current_filter->spill_slots) << 12;
  }
  action set_imm {
    op |= imm_check(u32_parse(std::string(start, fpc - start)));
  }
  action push_op {
    current_filter->ops.push_back(op);
    op = 0;
  }
  action opcode_mov {
    op |= static_cast<uint32_t>(LSMSB_OPCODE_MOV) << 24;
  }
  mov = ("mov" %opcode_mov) . ws . (reg >start %set_reg1) . "," . ws . (reg >start %set_reg2) . ws . (";" %push_op) . ws;

  action opcode_spill {
    op |= static_cast<uint32_t>(LSMSB_OPCODE_SPILL) << 24;
  }
  spill = ("spill" %opcode_spill) . ws . (slot >start %set_spill1) . "," . ws . (reg >start %set_reg3) . ws . (";" %push_op) . ws;

  action opcode_unspill {
    op |= static_cast<uint32_t>(LSMSB_OPCODE_UNSPILL) << 24;
  }
  unspill = ("unspill" %opcode_unspill) . ws . (reg >start %set_reg1) . "," . ws . (slot >start %set_spill2) . ws . (";" %push_op) . ws;

  action opcode_ldi {
    op |= static_cast<uint32_t>(LSMSB_OPCODE_LDI) << 24;
  }
  ldi = ("ldi" %opcode_ldi) . ws . (reg >start %set_reg1) . "," . ws . (u32 >start %set_imm) . ws . (";" %push_op) . ws;

  action opcode_ret {
    op |= static_cast<uint32_t>(LSMSB_OPCODE_RET) << 24;
  }
  ret = ("ret" %opcode_ret) . ws . (reg >start %set_reg1) . ws . (";" %push_op) . ws;

  reg_operands =
        (reg >start %set_reg1) . ws . "," . ws .
        (reg >start %set_reg2) . ws . "," . ws .
        (reg >start %set_reg3);

  action opcode_and {
    op |= static_cast<uint32_t>(LSMSB_OPCODE_AND) << 24;
  }
  and = ("and" %opcode_and) . ws .
        reg_operands . ws .
        (";" %push_op) . ws;

  action opcode_or {
    op |= static_cast<uint32_t>(LSMSB_OPCODE_OR) << 24;
  }
  or = ("or" %opcode_or) . ws .
        reg_operands . ws .
        (";" %push_op) . ws;

  action opcode_xor {
    op |= static_cast<uint32_t>(LSMSB_OPCODE_XOR) << 24;
  }
  xor = ("xor" %opcode_xor) . ws .
        reg_operands . ws .
        (";" %push_op) . ws;

  action opcode_eq {
    op |= static_cast<uint32_t>(LSMSB_OPCODE_EQ) << 24;
  }
  eq = ("eq" %opcode_eq) . ws .
        reg_operands . ws .
        (";" %push_op) . ws;

  action opcode_ne {
    op |= static_cast<uint32_t>(LSMSB_OPCODE_NE) << 24;
  }
  ne = ("ne" %opcode_ne) . ws .
        reg_operands . ws .
        (";" %push_op) . ws;

  action opcode_gt {
    op |= static_cast<uint32_t>(LSMSB_OPCODE_GT) << 24;
  }
  gt = ("gt" %opcode_gt) . ws .
        reg_operands . ws .
        (";" %push_op) . ws;

  action opcode_lt {
    op |= static_cast<uint32_t>(LSMSB_OPCODE_LT) << 24;
  }
  lt = ("lt" %opcode_lt) . ws .
        reg_operands . ws .
        (";" %push_op) . ws;

  action opcode_gte {
    op |= static_cast<uint32_t>(LSMSB_OPCODE_GTE) << 24;
  }
  gte = ("gte" %opcode_gte) . ws .
        reg_operands . ws .
        (";" %push_op) . ws;

  action opcode_lte {
    op |= static_cast<uint32_t>(LSMSB_OPCODE_LTE) << 24;
  }
  lte = ("lte" %opcode_lte) . ws .
        reg_operands . ws .
        (";" %push_op) . ws;

  action opcode_isprefixof {
    op |= static_cast<uint32_t>(LSMSB_OPCODE_ISPREFIXOF) << 24;
  }
  isprefixof = ("isprefixof" %opcode_isprefixof) . ws .
               reg_operands . ws .
               (";" %push_op) . ws;

  action set_const {
    const std::string constant_name(start, fpc - start);
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

  action opcode_ldc {
    op |= static_cast<uint32_t>(LSMSB_OPCODE_LDC) << 24;
  }
  ldc = ("ldc" %opcode_ldc) . ws . (reg >start %set_reg1) . "," . ws . (token >start %set_const) . ws . (";" %push_op) . ws;

  action jmp_mark {
    const std::string target = std::string(start, fpc - start);
    const std::map<std::string, std::vector<unsigned> >::iterator i =
      jmp_targets.find(target);

    if (i == jmp_targets.end()) {
      jmp_targets[target].push_back(current_filter->ops.size());
    } else {
      i->second.push_back(current_filter->ops.size());
    }
  }

  action opcode_jmp {
    op |= static_cast<uint32_t>(LSMSB_OPCODE_JMP) << 24;
  }
  jmp = ("jmp" %opcode_jmp) . ws . '#' . (token >start %jmp_mark) . ws . (";" %push_op) . ws;

  action opcode_jnz {
    op |= static_cast<uint32_t>(LSMSB_OPCODE_JNZ) << 24;
  }
  jnz = ("jnz" %opcode_jnz) . ws . (reg >start %set_reg1) . ws . "," . ws . '#' . (token >start %jmp_mark) . ws . (";" %push_op) . ws;

  action opcode_jz {
    op |= static_cast<uint32_t>(LSMSB_OPCODE_JZ) << 24;
  }
  jz = ("jz" %opcode_jz) . ws . (reg >start %set_reg1) . ws . "," . ws . '#' . (token >start %jmp_mark) . ws . (";" %push_op) . ws;

  action jump_resolve {
    const std::string target = std::string(start, fpc - start);
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
  jump_target = '#' . (token >start %jump_resolve) . ':' . ws;

  inst = jump_target | mov | spill | unspill | and | or | xor | eq | ne | gt | lt | gte | lte | ldc | ldi | jnz | jz | jmp | isprefixof | ret;

  filter = "filter" . ws . (token >start %filter_new) . ws . "{" . ws . constants? . spillslots? . inst* . ("}" @filter_push) . ws;

  as := ws . filter*;

  write data;
}%%

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

  %% write init;
  %% write exec;

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
