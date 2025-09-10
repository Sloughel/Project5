#include"stu.h"

int get_num_from_file(FILE*fp) {
	char ch; int num = 0; int sign = 1;
	
	while ((ch = fgetc(fp)) < '0' || ch > '9') {
		if (ch == '-') {
			sign = -1; 
			ch = fgetc(fp);
			break;
		}
		if (ch == EOF)return 0;
	}
	while (ch >= '0' && ch <= '9') {
		num = num * 10 + ch - '0';
		ch = fgetc(fp);
	}
	ungetc(ch, fp);
	return num * sign;
}

bool read_variables_and_clauses_num(FILE*fp,int*variable_number,int*clause_number) {
	char ch; char buffer[1024];
	while ((ch = fgetc(fp)) == 'c')if (fgets(buffer, sizeof(buffer), fp) == NULL)break;
	if (ch != EOF)ungetc(ch, fp);
	if ((ch = fgetc(fp)) == 'p')/*printf("find the 'p'\n")*/;
	else {
		printf("didn't find the p\n");
		return false;
	}
	*variable_number = get_num_from_file(fp); *clause_number = get_num_from_file(fp);
	if (*variable_number<=0 || *clause_number<=0) {
		printf("wrong in read variables and clauses num\n");
		return false;
	}
	printf("变量数为%d,子句数为%d\n", *variable_number, *clause_number);
	return true;
}

Literals* get_clauses_set(FILE* fp,int *size,int variables_number) {
	*size = 0;//init size

	int temp_num; int max_size = 10;
	Literals* literals = NULL;
	literals= (Literals*)malloc(sizeof(Literals) * max_size);
	if (literals == NULL) {
		printf("fail to allocate memory for literal in get clauses set \n");
		goto error;
	}//init literals

	for (temp_num = get_num_from_file(fp); temp_num != 0; temp_num = get_num_from_file(fp)) {
		literals[*size].value = abs(temp_num);
		if (literals[*size].value > variables_number) goto error;//to prevent overflow
		literals[(*size)++].sign = temp_num > 0 ? true : false;//to complete value and sign in Literals

		if (*size == max_size) {
			max_size += 10;
			Literals* new_literals = (Literals*)realloc(literals, max_size * (sizeof(Literals)));
			if (new_literals == NULL) {
				printf("fail to realloc new_literals\n");
				goto error;
			}//realloc
			literals = new_literals;
		}
	}

	return literals;

error:
	if (literals != NULL)free(literals);
	return NULL;
}

bool add_clauses(solver*s,Literals *literals,int clauses_idx,int size,int variables_number) {
	if (literals == NULL)return false;

	Clause* c = &s->clauses[clauses_idx];
	c->literals = (Literals*)malloc(size * sizeof(Literals));
	if (c->literals == NULL) {
		printf("fail to allocate memory for c->literals\n");
		return false;
	}//init c->literals

	memcpy(c->literals, literals, size * sizeof(Literals));//copy

	c->size = size;
	c->watch1 = 0;
	c->watch2 = size > 1 ? 1 : 0;//init variables under Clauses

	int value_idx;
	for (int i = 0; i < size; i++) {
		value_idx = literals[i].value - 1;
		if (value_idx<0 || value_idx>variables_number - 1) {
			printf("wrong with the value_idx\n");
			return false;
		}
		Variable *var = &s->variables[value_idx];//find the variable 

		var->activity += 1;// to add activity

		if (literals[i].sign)var->pos_clauses[var->pos_count++] = c;
		else var->neg_clauses[var->neg_count++] = c;	//watch clauses
	}
	return true;
}
bool add(solver* s, FILE* input, int clauses_number, int variables_number) {
	Literals* literals; int size = 0;
	for (int i = 0; i < clauses_number; i++) {
		literals = get_clauses_set(input, &size, variables_number);
		if (!add_clauses(s, literals, i, size, variables_number)) {
			for (int j = 0; j < i; j++)free(s->clauses[j].literals);
			free(literals);
			return false;
		}
		free(literals);
	}
	return true;
}