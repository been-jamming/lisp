#include "dictionary.h"

typedef enum data_type data_type;

enum data_type{
	NONE_DATA,
	INT_DATA,
	IDENTIFIER,
	S_EXPR,
	Q_EXPR,
	BUILTIN_FUNCTION,
	FUNCTION
};

typedef struct data data;

struct data{
	data_type type;
	union{
		int int_value;
		char *identifier_name;
		struct{
			int num_entries;
			int *entries;
		};
		struct{
			int var_list;
			int source;
		};
		int (*builtin_function)(int, int *);
	};
	int num_references;
};

typedef struct scope scope;

struct scope{
	int level;
	dictionary variables;
	scope *previous;
	scope *next;
};

typedef struct variable variable;

struct variable{
	char *name;
	int data_index;
};

typedef struct shadow_stack shadow_stack;

struct shadow_stack{
	shadow_stack *previous;
	int data_index;
};

extern data *data_heap;
extern unsigned int num_allocated;
extern scope *global_scope;
extern scope *current_scope;

int initialize_heap(int num_entries);
int create_global_scope();
int next_scope();
void free_variable(void *v);
void clear_scope();
void previous_scope();
void mark_protected(int data_index);
void mark_unprotected(int data_index);
void mark_allocated(int data_index);
void mark_allocated_recursive(int data_index);
void mark_variable_data(void *v);
void garbage_collect();
int allocate();
void decrement_references(int data_index);
int push_shadow_stack(int data_index);
int pop_shadow_stack();
void clear_shadow_stack();
shadow_stack *get_shadow_stack();
void set_shadow_stack(shadow_stack *next_stack);

