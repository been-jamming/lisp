#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include "allocate.h"
#include "dictionary.h"

int global_none;

int is_whitespace(char c){
	return c == ' ' || c == '\t' || c == '\r' || c == '\n';
}

void skip_whitespace(char **c){
	while(is_whitespace(**c)){
		++*c;
	}
}

int is_digit(char c){
	return c >= '0' && c <= '9';
}

int is_identifier_char(char c){
	return !is_whitespace(c) && c && c != '(' && c != ')' && c != '{' && c != '}';
}

int get_integer(char **c){
	int output = 0;

	if(**c == '-'){
		++*c;
		return -get_integer(c);
	}

	while(is_digit(**c)){
		output *= 10;
		output += **c - '0';
		++*c;
	}

	skip_whitespace(c);

	return output;
}

char *get_identifier_name(char **c){
	char *beginning;
	char *output;

	beginning = *c;
	while(is_identifier_char(**c)){
		++*c;
	}

	output = malloc(sizeof(char)*(*c - beginning + 1));
	if(!output){
		return NULL;
	}

	memcpy(output, beginning, sizeof(char)*(*c - beginning));
	output[*c - beginning] = '\0';
	skip_whitespace(c);

	return output;
}

int get_quoted_identifier(char **c){
	char *name;
	int output;

	name = get_identifier_name(c);
	if(!name){
		return -1;
	}
	output = allocate();
	if(output == -1){
		return -1;
	}
	data_heap[output].type = IDENTIFIER;
	data_heap[output].identifier_name = name;

	return output;
}

int get_integer_data(char **c){
	int output;
	int int_value;

	int_value = get_integer(c);
	output = allocate();
	if(output == -1){
		return -1;
	}
	data_heap[output].type = INT_DATA;
	data_heap[output].int_value = int_value;

	return output;
}

int get_quoted_value(char **c);

int get_quoted_expression(char **c, data_type type){
	char end_char;
	int output;
	int value;
	int i;
	int *next_entries;

	if(type == S_EXPR){
		end_char = ')';
	} else {
		end_char = '}';
	}

	output = allocate();
	if(output == -1){
		return -1;
	}
	if(!push_shadow_stack(output)){
		return -1;
	}
	data_heap[output].num_entries = 0;
	data_heap[output].entries = NULL;

	skip_whitespace(c);
	while(**c != end_char){
		value = get_quoted_value(c);
		if(value == -1){
			return -1;
		}
		push_shadow_stack(value);
		data_heap[output].num_entries++;
		next_entries = realloc(data_heap[output].entries, sizeof(int)*data_heap[output].num_entries);
		if(!next_entries){
			return -1;
		}
		data_heap[output].entries = next_entries;
		data_heap[output].entries[data_heap[output].num_entries - 1] = value;
		skip_whitespace(c);
	}

	++*c;
	skip_whitespace(c);

	for(i = 0; i <= data_heap[output].num_entries; i++){
		pop_shadow_stack();
	}
	data_heap[output].type = type;

	return output;
}

int get_quoted_value(char **c){
	skip_whitespace(c);
	if(is_digit(**c)){
		return get_integer_data(c);
	} else if(is_identifier_char(**c)){
		return get_quoted_identifier(c);
	} else if(**c == '('){
		++*c;
		return get_quoted_expression(c, S_EXPR);
	} else if(**c == '{'){
		++*c;
		return get_quoted_expression(c, Q_EXPR);
	} else {
		return -1;
	}
}

void print_value(int value){
	int i;

	switch(data_heap[value].type){
		case INT_DATA:
			printf("%d", data_heap[value].int_value);
			return;
		case IDENTIFIER:
			printf("%s", data_heap[value].identifier_name);
			return;
		case S_EXPR:
			printf("(");
			for(i = 0; i < data_heap[value].num_entries; i++){
				print_value(data_heap[value].entries[i]);
				if(i < data_heap[value].num_entries - 1){
					printf(" ");
				}
			}
			printf(")");
			return;
		case Q_EXPR:
			printf("{");
			for(i = 0; i < data_heap[value].num_entries; i++){
				print_value(data_heap[value].entries[i]);
				if(i < data_heap[value].num_entries - 1){
					printf(" ");
				}
			}
			printf("}");
			return;
		case NONE_DATA:
			printf("none");
			return;
		case BUILTIN_FUNCTION:
			printf("[builtin_function]");
			return;
		case FUNCTION:
			printf("[function]:");
			print_value(data_heap[value].var_list);
			printf(",");
			print_value(data_heap[value].source);
			return;
	}
}

int set_variable(char *var_name, int data_index){
	variable *var;

	var = read_dictionary(current_scope->variables, var_name, 0);
	if(!var){
		var = malloc(sizeof(variable));
		if(!var){
			return 0;
		}
		var->name = malloc(sizeof(char)*(strlen(var_name) + 1));
		if(!var->name){
			free(var);
			return 0;
		}
		var->data_index = data_index;
		data_heap[data_index].num_references++;
		write_dictionary(&(current_scope->variables), var_name, var, 0);
		return 1;
	} else {
		decrement_references(var->data_index);
		var->data_index = data_index;
		data_heap[data_index].num_references++;
		return 1;
	}
}

int evaluate_q_expression(int data_index, int expand_q_expr);

int execute_s_expr(int data_index){
	int *entries;
	int *next_entries;
	int next_data_index;
	int output;
	int i;
	int made_scope = 0;
	shadow_stack *first_entry;
	shadow_stack *prev_shadow_stack;
	shadow_stack *current_shadow_stack;

	push_shadow_stack(data_index);
	data_heap[data_index].num_references++;
	do{
		if(data_heap[data_index].num_entries == 0){
			return -1;
		}
		entries = malloc(sizeof(int)*data_heap[data_index].num_entries);
		if(!entries){
			return -1;
		}
		for(i = 0; i < data_heap[data_index].num_entries; i++){
			entries[i] = evaluate_q_expression(data_heap[data_index].entries[i], 0);
			if(entries[i] == -1){
				return -1;
			}
			push_shadow_stack(entries[i]);
		}
		prev_shadow_stack = get_shadow_stack();
		if(data_heap[entries[0]].type == FUNCTION && !next_scope()){
			return -1;
		} else if(data_heap[entries[0]].type == FUNCTION){
			made_scope = 1;
		}
		while(data_heap[entries[0]].type == FUNCTION){
			clear_scope();
			if(data_heap[data_heap[entries[0]].var_list].type != Q_EXPR){
				return -1;
			}
			if(data_heap[data_heap[entries[0]].var_list].num_entries != data_heap[data_index].num_entries - 1){
				return -1;
			}
			for(i = 0; i < data_heap[data_heap[entries[0]].var_list].num_entries; i++){
				if(data_heap[data_heap[data_heap[entries[0]].var_list].entries[i]].type != IDENTIFIER){
					return -1;
				}
				if(!set_variable(data_heap[data_heap[data_heap[entries[0]].var_list].entries[i]].identifier_name, entries[i + 1])){
					return -1;
				}
			}
			next_data_index = data_heap[entries[0]].source;
			if(data_heap[next_data_index].type != Q_EXPR){
				return -1;
			}
			if(data_heap[next_data_index].num_entries == 0){
				return -1;
			}
			push_shadow_stack(next_data_index);
			data_heap[next_data_index].num_references++;
			first_entry = get_shadow_stack();
			next_entries = malloc(sizeof(int)*data_heap[next_data_index].num_entries);
			if(!next_entries){
				return -1;
			}
			for(i = 0; i < data_heap[next_data_index].num_entries; i++){
				next_entries[i] = evaluate_q_expression(data_heap[next_data_index].entries[i], 0);
				if(next_entries[i] == -1){
					return -1;
				}
				push_shadow_stack(next_entries[i]);
			}
			current_shadow_stack = get_shadow_stack();
			set_shadow_stack(prev_shadow_stack);
			for(i = 0; i < data_heap[data_index].num_entries; i++){
				decrement_references(pop_shadow_stack());
			}
			decrement_references(pop_shadow_stack());
			free(entries);
			entries = next_entries;
			data_index = next_data_index;
			first_entry->previous = get_shadow_stack();
			set_shadow_stack(current_shadow_stack);
			prev_shadow_stack = current_shadow_stack;
		}
		if(data_heap[entries[0]].type != BUILTIN_FUNCTION){
			return -1;
		}
		output = data_heap[entries[0]].builtin_function(data_heap[data_index].num_entries, entries);
		for(i = 0; i < data_heap[data_index].num_entries; i++){
			decrement_references(pop_shadow_stack());
		}
		decrement_references(pop_shadow_stack());
		free(entries);
	} while(0);//add while here
	if(made_scope){
		previous_scope();
	}
	return output;
}

int evaluate_q_expression(int data_index, int expand_q_expr){
	int output;
	int *entries = NULL;
	int *next_entries;
	int i;
	int added_scope = 0;
	int next_data_index;
	int original_data_index;
	scope *search_scope;
	variable *var;
	shadow_stack *current_shadow_stack;
	shadow_stack *prev_shadow_stack;
	shadow_stack *first_entry;

	switch(data_heap[data_index].type){
		case INT_DATA:
			output = allocate();
			if(output == -1){
				return -1;
			}
			data_heap[output].type = INT_DATA;
			data_heap[output].int_value = data_heap[data_index].int_value;
			return output;
		case IDENTIFIER:
			search_scope = current_scope;
			while(search_scope){
				var = read_dictionary(search_scope->variables, data_heap[data_index].identifier_name, 0);
				if(var){
					output = var->data_index;
					data_heap[output].num_references++;
					return output;
				}
				search_scope = search_scope->previous;
			}
			return -1;
		case Q_EXPR:
		case S_EXPR:
			if(data_heap[data_index].type == S_EXPR || expand_q_expr){
				return execute_s_expr(data_index);
			} else {
				data_heap[data_index].num_references++;
				return data_index;
			}
			/*
			if(data_heap[data_index].type == S_EXPR || expand_q_expr){
				if(data_heap[data_index].num_entries == 0){
					return -1;
				}
				entries = malloc(sizeof(int)*data_heap[data_index].num_entries);
				if(!entries){
					return -1;
				}
				for(i = 0; i < data_heap[data_index].num_entries; i++){
					entries[i] = evaluate_q_expression(data_heap[data_index].entries[i], 0);
					if(entries[i] == -1){
						return -1;
					}
					push_shadow_stack(entries[i]);
				}
				if(data_heap[entries[0]].type == BUILTIN_FUNCTION){
					output = data_heap[entries[0]].builtin_function(data_heap[data_index].num_entries, entries);
				} else if(data_heap[entries[0]].type == FUNCTION){
					if(data_heap[data_heap[entries[0]].var_list].type != Q_EXPR){
						return -1;
					}
					if(data_heap[data_heap[entries[0]].var_list].num_entries != data_heap[data_index].num_entries - 1){
						return -1;
					}
					if(!next_scope()){
						return -1;
					}
					for(i = 0; i < data_heap[data_heap[entries[0]].var_list].num_entries; i++){
						if(data_heap[data_heap[data_heap[entries[0]].var_list].entries[i]].type != IDENTIFIER){
							return -1;
						}
						if(!set_variable(data_heap[data_heap[data_heap[entries[0]].var_list].entries[i]].identifier_name, entries[i + 1])){
							return -1;
						}
					}
					if(data_heap[data_heap[entries[0]].source].type != Q_EXPR){
						return -1;
					}
					output = evaluate_q_expression(data_heap[entries[0]].source, 1);
					previous_scope();
				} else {
					return -1;
				}
				for(i = 0; i < data_heap[data_index].num_entries; i++){
					decrement_references(pop_shadow_stack());
				}
				free(entries);
				return output;
			} else {
				data_heap[data_index].num_references++;
				return data_index;
			}
			*/
		case BUILTIN_FUNCTION:
		case FUNCTION:
			data_heap[data_index].num_references++;
			return data_index;
		case NONE_DATA:
	}

	return -1;
}

int register_builtin_function(char *name, int (*builtin_function)(int, int *)){
	int data_index;
	variable *var;

	data_index = allocate();
	if(data_index == -1){
		return -1;
	}
	data_heap[data_index].type = BUILTIN_FUNCTION;
	data_heap[data_index].builtin_function = builtin_function;
	var = malloc(sizeof(variable));
	if(!var){
		decrement_references(data_index);
		return -1;
	}
	var->name = malloc(sizeof(char)*(strlen(name) + 1));
	if(!var->name){
		free(var);
		decrement_references(data_index);
		return -1;
	}
	strcpy(var->name, name);
	var->data_index = data_index;

	write_dictionary(&(global_scope->variables), name, var, 0);
	return data_index;
}

int data_equal(int b, int a){
	int i;

	if(data_heap[a].type != data_heap[b].type){
		return 0;
	}

	switch(data_heap[a].type){
		case NONE_DATA:
			return 1;
		case INT_DATA:
			return data_heap[a].int_value == data_heap[b].int_value;
		case IDENTIFIER:
			return !strcmp(data_heap[a].identifier_name, data_heap[b].identifier_name);
		case S_EXPR:
		case Q_EXPR:
			if(data_heap[a].num_entries != data_heap[b].num_entries){
				return 0;
			}
			for(i = 0; i < data_heap[a].num_entries; i++){
				if(!data_equal(data_heap[a].entries[i], data_heap[b].entries[i])){
					return 0;
				}
			}
			return 1;
		case BUILTIN_FUNCTION:
			return data_heap[a].builtin_function == data_heap[b].builtin_function;
		case FUNCTION:
			return data_equal(data_heap[a].var_list, data_heap[b].var_list) && data_equal(data_heap[a].source, data_heap[b].source);
	}

	return 0;
}

int add(int num_args, int *args){
	int output = 0;
	int output_index;
	int i;

	for(i = 1; i < num_args; i++){
		if(data_heap[args[i]].type != INT_DATA){
			return -1;
		}
		output += data_heap[args[i]].int_value;
	}

	output_index = allocate();
	if(output_index == -1){
		return -1;
	}
	data_heap[output_index].type = INT_DATA;
	data_heap[output_index].int_value = output;

	return output_index;
}

int multiply(int num_args, int *args){
	int output = 1;
	int output_index;
	int i;

	for(i = 1; i < num_args; i++){
		if(data_heap[args[i]].type != INT_DATA){
			return -1;
		}
		output *= data_heap[args[i]].int_value;
	}

	output_index = allocate();
	if(output_index == -1){
		return -1;
	}
	data_heap[output_index].type = INT_DATA;
	data_heap[output_index].int_value = output;

	return output_index;
}

int subtract(int num_args, int *args){
	int output;
	int output_index;
	int i;

	if(num_args == 2){
		if(data_heap[args[1]].type != INT_DATA){
			return -1;
		}
		output = -data_heap[args[1]].int_value;
	} else if(num_args > 2){
		if(data_heap[args[1]].type != INT_DATA){
			return -1;
		}
		output = data_heap[args[1]].int_value;
		for(i = 2; i < num_args; i++){
			if(data_heap[args[i]].type != INT_DATA){
				return -1;
			}
			output -= data_heap[args[i]].int_value;
		}
	} else {
		return -1;
	}

	output_index = allocate();
	if(output_index == -1){
		return -1;
	}
	data_heap[output_index].type = INT_DATA;
	data_heap[output_index].int_value = output;

	return output_index;
}

int divide(int num_args, int *args){
	int output;
	int output_index;
	int i;

	if(num_args <= 2){
		return -1;
	}

	if(data_heap[args[1]].type != INT_DATA){
		return -1;
	}
	output = data_heap[args[1]].int_value;
	for(i = 2; i < num_args; i++){
		if(data_heap[args[i]].type != INT_DATA){
			return -1;
		}
		output /= data_heap[args[i]].int_value;
	}

	output_index = allocate();
	if(output_index == -1){
		return -1;
	}
	data_heap[output_index].type = INT_DATA;
	data_heap[output_index].int_value = output;

	return output_index;
}

int lambda(int num_args, int *args){
	int output_index;

	if(num_args != 3){
		return -1;
	}

	output_index = allocate();
	if(output_index == -1){
		return -1;
	}
	data_heap[output_index].type = FUNCTION;
	data_heap[output_index].var_list = args[1];
	data_heap[output_index].source = args[2];
	data_heap[args[1]].num_references++;
	data_heap[args[2]].num_references++;

	return output_index;
}

int set(int num_args, int *args){
	int i;

	if(data_heap[args[1]].type != Q_EXPR){
		return -1;
	}

	if(num_args != data_heap[args[1]].num_entries + 2){
		return -1;
	}

	for(i = 0; i < data_heap[args[1]].num_entries; i++){
		if(data_heap[data_heap[args[1]].entries[i]].type != IDENTIFIER){
			return -1;
		}
		if(!set_variable(data_heap[data_heap[args[1]].entries[i]].identifier_name, args[i + 2])){
			return -1;
		}
	}

	data_heap[global_none].num_references++;
	return global_none;
}

int set_index(int num_args, int *args){
	if(num_args != 4){
		return -1;
	}
	if(data_heap[args[1]].type != Q_EXPR || data_heap[args[2]].type != INT_DATA){
		return -1;
	}
	if(data_heap[args[2]].int_value < 0 || data_heap[args[2]].int_value >= data_heap[args[1]].num_entries){
		return -1;
	}

	decrement_references(data_heap[args[1]].entries[data_heap[args[2]].int_value]);
	data_heap[args[1]].entries[data_heap[args[2]].int_value] = args[3];
	data_heap[args[3]].num_references++;
	data_heap[global_none].num_references++;
	return global_none;
}

int equal(int num_args, int *args){
	int output = 1;
	int output_index;
	int i;

	if(num_args < 2){
		return -1;
	}

	for(i = 2; i < num_args; i++){
		if(!data_equal(args[i], args[1])){
			output = 0;
		}
	}

	output_index = allocate();
	if(output_index == -1){
		return -1;
	}
	data_heap[output_index].type = INT_DATA;
	data_heap[output_index].int_value = output;

	return output_index;
}

int not_equal(int num_args, int *args){
	int output = 0;
	int output_index;
	int i;

	if(num_args < 2){
		return -1;
	}

	for(i = 2; i < num_args; i++){
		if(!data_equal(args[i], args[1])){
			output = 1;
		}
	}

	output_index = allocate();
	if(output_index == -1){
		return -1;
	}
	data_heap[output_index].type = INT_DATA;
	data_heap[output_index].int_value = output;

	return output_index;
}

int if_func(int num_args, int *args){
	if((num_args == 3 || num_args == 4) && data_heap[args[1]].type == INT_DATA && data_heap[args[1]].int_value != 0){
		return evaluate_q_expression(args[2], 1);
	} else if(num_args == 4){
		return evaluate_q_expression(args[3], 1);
	}

	return -1;
}

int while_func(int num_args, int *args){
	int data_index;

	if(num_args != 3){
		return -1;
	}

	data_index = evaluate_q_expression(args[1], 1);
	if(data_index == -1){
		return -1;
	}
	while(data_heap[data_index].type == INT_DATA && data_heap[data_index].int_value != 0){
		decrement_references(data_index);
		data_index = evaluate_q_expression(args[2], 1);
		if(data_index == -1){
			return -1;
		}
		decrement_references(data_index);
		data_index = evaluate_q_expression(args[1], 1);
		if(data_index == -1){
			return -1;
		}
	}
	decrement_references(data_index);

	data_heap[global_none].num_references++;
	return global_none;
}

int colon_func(int num_args, int *args){
	if(num_args == 1){
		data_heap[global_none].num_references++;
		return global_none;
	}

	data_heap[args[num_args - 1]].num_references++;
	return args[num_args - 1];
}

int index_func(int num_args, int *args){
	if(num_args != 3){
		return -1;
	}
	if(data_heap[args[1]].type != Q_EXPR || data_heap[args[2]].type != INT_DATA){
		return -1;
	}
	if(data_heap[args[2]].int_value < 0 || data_heap[args[2]].int_value >= data_heap[args[1]].num_entries){
		return -1;
	}

	return evaluate_q_expression(data_heap[args[1]].entries[data_heap[args[2]].int_value], 0);
}

int head(int num_args, int *args){
	int *new_entries;
	int *less_entries;
	int output_index;
	int i;

	if(num_args <= 1){
		return -1;
	}
	new_entries = malloc(sizeof(int)*(num_args - 1));
	if(!new_entries){
		return -1;
	}

	for(i = 1; i < num_args; i++){
		if(data_heap[args[i]].type != Q_EXPR || data_heap[args[i]].num_entries == 0){
			return -1;
		}
		new_entries[i - 1] = data_heap[args[i]].entries[0];
		data_heap[new_entries[i - 1]].num_references++;
		data_heap[args[i]].num_entries--;
		memmove(data_heap[args[i]].entries, data_heap[args[i]].entries + 1, sizeof(int)*data_heap[args[i]].num_entries);
		if(data_heap[args[i]].num_entries > 0){
			less_entries = realloc(data_heap[args[i]].entries, sizeof(int)*data_heap[args[i]].num_entries);
			if(!less_entries){
				return -1;
			}
		} else {
			less_entries = NULL;
		}
		data_heap[args[i]].entries = less_entries;
	}

	output_index = allocate();
	if(output_index == -1){
		return -1;
	}
	data_heap[output_index].type = Q_EXPR;
	data_heap[output_index].num_entries = num_args - 1;
	data_heap[output_index].entries = new_entries;

	return output_index;
}

int pop(int num_args, int *args){
	int *less_entries;
	int output_index;

	if(num_args != 2){
		return -1;
	}

	if(data_heap[args[1]].type != Q_EXPR || data_heap[args[1]].num_entries == 0){
		return -1;
	}

	data_heap[data_heap[args[1]].entries[0]].num_references++;
	output_index = data_heap[args[1]].entries[0];

	data_heap[args[1]].num_entries--;
	memmove(data_heap[args[1]].entries, data_heap[args[1]].entries + 1, sizeof(int)*data_heap[args[1]].num_entries);
	if(data_heap[args[1]].num_entries > 0){
		less_entries = realloc(data_heap[args[1]].entries, sizeof(int)*data_heap[args[1]].num_entries);
		if(!less_entries){
			return -1;
		}
		data_heap[args[1]].entries = less_entries;
	} else {
		data_heap[args[1]].entries = NULL;
	}

	return output_index;
}

int push(int num_args, int *args){
	int *more_entries;
	int output_index;

	if(num_args != 3){
		return -1;
	}

	if(data_heap[args[1]].type != Q_EXPR){
		return -1;
	}

	data_heap[args[2]].num_references++;
	data_heap[args[1]].num_references++;
	output_index = args[1];

	data_heap[args[1]].num_entries++;
	more_entries = realloc(data_heap[args[1]].entries, sizeof(int)*data_heap[args[1]].num_entries);
	if(!more_entries){
		return -1;
	}
	data_heap[args[1]].entries = more_entries;
	memmove(data_heap[args[1]].entries + 1, data_heap[args[1]].entries, sizeof(int)*(data_heap[args[1]].num_entries - 1));
	data_heap[args[1]].entries[0] = args[2];

	return output_index;
}

int eval(int num_args, int *args){
	int output_index = -1;
	int i;

	for(i = 1; i < num_args; i++){
		if(output_index != -1){
			decrement_references(output_index);
		}
		if(data_heap[args[i]].type != Q_EXPR){
			return -1;
		}
		output_index = evaluate_q_expression(args[i], 1);
		if(output_index == -1){
			return -1;
		}
	}

	return output_index;
}

int main(int argc, char **argv){
	char input[256];
	char *input_pointer;
	int data;
	int result;

	if(!initialize_heap(10000)){
		fprintf(stderr, "Error: failed to initialize heap\n");
		return 1;
	}
	if(!create_global_scope()){
		fprintf(stderr, "Error: failed to create global scope\n");
		return 1;
	}
	data = allocate();
	if(data == -1){
		fprintf(stderr, "Error: allocation failed\n");
		return 1;
	}
	data_heap[data].type = NONE_DATA;
	push_shadow_stack(data);
	global_none = data;
	register_builtin_function("+", add);
	register_builtin_function("-", subtract);
	register_builtin_function("*", multiply);
	register_builtin_function("/", divide);
	register_builtin_function("\\", lambda);
	register_builtin_function("set", set);
	register_builtin_function("=", equal);
	register_builtin_function("!=", not_equal);
	register_builtin_function("if", if_func);
	register_builtin_function("while", while_func);
	register_builtin_function(":", colon_func);
	register_builtin_function("head", head);
	register_builtin_function("pop", pop);
	register_builtin_function("push", push);
	register_builtin_function("eval", eval);
	register_builtin_function("index", index_func);
	register_builtin_function("seti", set_index);
	while(1){
		printf("lisp> ");
		fgets(input, 256, stdin);
		input_pointer = input;
		data = get_quoted_value(&input_pointer);
		push_shadow_stack(data);
		if(data == -1){
			fprintf(stderr, "Error: failed to parse expression\n");
			clear_shadow_stack();
			push_shadow_stack(global_none);
			continue;
		}
		result = evaluate_q_expression(data, 0);
		if(result == -1){
			fprintf(stderr, "Error: failed to evaluate expression\n");
			clear_shadow_stack();
			push_shadow_stack(global_none);
			decrement_references(data);
			continue;
		}

		print_value(result);
		pop_shadow_stack();
		decrement_references(data);
		decrement_references(result);
		printf("\nnum_allocated: %d\n", num_allocated);
	}

	return 0;
}

