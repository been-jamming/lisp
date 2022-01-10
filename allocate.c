#include <stdlib.h>
#include <stdio.h>
#include "dictionary.h"
#include "allocate.h"

data *data_heap;
static unsigned int *data_heap_allocation;
static unsigned int *data_heap_locations;
static unsigned int data_heap_size;
unsigned int num_allocated;
scope *global_scope;
scope *current_scope;
static shadow_stack *stack;
static unsigned int shadow_stack_size = 0;

int initialize_heap(int num_entries){
	int i;

	data_heap = malloc(sizeof(data)*num_entries);
	if(!data_heap){
		return 0;
	}
	data_heap_size = num_entries;
	data_heap_allocation = malloc(sizeof(unsigned int)*num_entries);
	if(!data_heap_allocation){
		free(data_heap);
		return 0;
	}
	data_heap_locations = malloc(sizeof(unsigned int)*num_entries);
	if(!data_heap_locations){
		free(data_heap);
		free(data_heap_allocation);
		return 0;
	}
	num_allocated = 0;
	for(i = 0; i < num_entries; i++){
		data_heap[i].type = NONE_DATA;
		data_heap[i].num_references = 0;
		data_heap_allocation[i] = i;
		data_heap_locations[i] = i;
	}
	stack = NULL;

	return 1;
}

int create_global_scope(){
	global_scope = malloc(sizeof(scope));
	if(!global_scope){
		return 0;
	}
	global_scope->variables = create_dictionary(NULL);
	global_scope->level = 0;
	global_scope->previous = NULL;
	global_scope->next = NULL;

	current_scope = global_scope;

	return 1;
}

int next_scope(){
	scope *next;

	next = malloc(sizeof(scope));
	if(!next){
		return 0;
	}
	next->variables = create_dictionary(NULL);
	next->level = current_scope->level + 1;
	next->previous = current_scope;
	next->next = NULL;

	current_scope->next = next;
	current_scope = next;

	return 1;
}

void free_variable(void *v){
	variable *var;

	var = v;
	decrement_references(var->data_index);
	free(var->name);
	free(var);
}

void clear_scope(){
	free_dictionary(&(current_scope->variables), free_variable);
}

void previous_scope(){
	scope *previous;

	previous = current_scope->previous;
	free_dictionary(&(current_scope->variables), free_variable);
	free(current_scope);
	current_scope = previous;

	current_scope->next = NULL;
}

void mark_allocated(int data_index){
	int temp_index;

	if(0 && data_index == data_heap_allocation[num_allocated]){
		num_allocated++;
	} else {
		temp_index = data_heap_allocation[num_allocated];
		data_heap_allocation[num_allocated] = data_index;
		data_heap_allocation[data_heap_locations[data_index]] = temp_index;
		data_heap_locations[temp_index] = data_heap_locations[data_index];
		data_heap_locations[data_index] = num_allocated;

		num_allocated++;
	}
}

void mark_deallocated(int data_index){
	//Often, data is deallocated in the reverse order that it was allocated
	if(0 && data_index == data_heap_allocation[num_allocated - 1]){
		num_allocated--;
	} else {
		num_allocated--;

		//Again, this is confusing but it's the same swap as before
		mark_allocated(data_index);

		num_allocated--;
	}
}

void mark_allocated_recursive(int data_index){
	int i;

	if(data_heap_locations[data_index] < num_allocated){
		return;
	}

	mark_allocated(data_index);

	if(data_heap[data_index].type == S_EXPR || data_heap[data_index].type == Q_EXPR){
		for(i = 0; i < data_heap[data_index].num_entries; i++){
			mark_allocated_recursive(data_heap[data_index].entries[i]);
		}
	} else if(data_heap[data_index].type == FUNCTION){
		mark_allocated_recursive(data_heap[data_index].var_list);
		mark_allocated_recursive(data_heap[data_index].source);
	}
}

void mark_variable_data(void *v){
	variable *var;

	var = v;
	mark_allocated_recursive(var->data_index);
}

void garbage_collect(){
	scope *search_scope;
	shadow_stack *stack_place;

	printf("garbage collecting...\n");
	num_allocated = 0;
	search_scope = global_scope;
	while(search_scope){
		iterate_dictionary(search_scope->variables, mark_variable_data);
		search_scope = search_scope->next;
	}

	stack_place = stack;
	while(stack_place){
		mark_allocated_recursive(stack_place->data_index);
		stack_place = stack_place->previous;
	}
	printf("after garbage collection: %d\n", num_allocated);
}

int allocate(){
	if(num_allocated >= data_heap_size){
		garbage_collect();
		if(num_allocated >= data_heap_size){
			fprintf(stderr, "Error: Out of memory!\n");
			return -1;
		}
	}

	if(data_heap[data_heap_allocation[num_allocated]].type == IDENTIFIER){
		free(data_heap[data_heap_allocation[num_allocated]].identifier_name);
	} else if(data_heap[data_heap_allocation[num_allocated]].type == S_EXPR || data_heap[data_heap_allocation[num_allocated]].type == Q_EXPR){
		free(data_heap[data_heap_allocation[num_allocated]].entries);
	}

	data_heap[data_heap_allocation[num_allocated]].num_references = 1;
	num_allocated++;
	return data_heap_allocation[num_allocated - 1];
}

void decrement_references(int data_index){
	int i;

	data_heap[data_index].num_references--;
	if(data_heap[data_index].num_references == 0){
		if(data_heap[data_index].type == Q_EXPR || data_heap[data_index].type == S_EXPR){
			for(i = 0; i < data_heap[data_index].num_entries; i++){
				decrement_references(data_heap[data_index].entries[i]);
			}
		} else if(data_heap[data_index].type == FUNCTION){
			decrement_references(data_heap[data_index].var_list);
			decrement_references(data_heap[data_index].source);
		}
		mark_deallocated(data_index);
	}
}

int push_shadow_stack(int data_index){
	shadow_stack *next;

	next = malloc(sizeof(shadow_stack));
	if(!next){
		return 0;
	}
	next->previous = stack;
	next->data_index = data_index;
	stack = next;
	shadow_stack_size++;

	return 1;
}

int pop_shadow_stack(){
	shadow_stack *previous;
	int output;

	previous = stack->previous;
	output = stack->data_index;
	free(stack);
	stack = previous;
	shadow_stack_size--;

	return output;
}

void clear_shadow_stack(){
	while(stack){
		pop_shadow_stack();
	}
}

shadow_stack *get_shadow_stack(){
	return stack;
}

void set_shadow_stack(shadow_stack *next_stack){
	stack = next_stack;
}
