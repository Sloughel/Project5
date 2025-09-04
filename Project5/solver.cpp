#include"stu.h"

solver* init_solver(FILE*input,int variables_number,int clause_number) {
	solver*s = (solver*)calloc(1,sizeof(solver));
	if (s == NULL)goto error;  //init s
	s->clauses = NULL;
	s->var_count = variables_number;
	s->clause_count = clause_number;
	s->var_increasement = 1.0;
	s->decision_level = 0;  //init variables under s

	s->clauses = (Clause*)malloc(clause_number*sizeof(Clause));
	for (int i = 0; i < clause_number; i++)s->clauses[i].literals = NULL;
	s->variables = (Variable*)calloc(variables_number,sizeof(Variable));
	s->trail = (int*)malloc(sizeof(int) * variables_number);
	s->trail_level = (int*)malloc(sizeof(int) * variables_number);
	if (!s->clauses || !s->variables || !s->trail || !s->trail_level)goto error;//init variables under s which need allocate memory
	
	for (int i = 0; i < variables_number; i++) {  //init s->variable
		s->variables[i].assignment = UNSIGNNED;
		s->variables[i].decision_level = -1;  //init variables under s->variable

		s->variables[i].neg_clauses = (Clause**)malloc(clause_number*sizeof(Clause*));
		s->variables[i].pos_clauses = (Clause**)malloc(clause_number*sizeof(Clause*));
		if (s->variables[i].neg_clauses == NULL || s->variables[i].pos_clauses == NULL) goto error;//init variables under s->variable which need allocate memory
	}
	if (!add(s, input, clause_number, variables_number))goto error;//init variables under s->clauses

	for (int i = 0; i < variables_number; i++) {
		Clause** new_neg_clauses = (Clause**)realloc(s->variables[i].neg_clauses, sizeof(Clause*) * s->variables[i].neg_count);
		Clause** new_pos_clauses = (Clause**)realloc(s->variables[i].pos_clauses, sizeof(Clause*) * s->variables[i].pos_count);
		if (!new_neg_clauses || !new_pos_clauses) {
			free(new_neg_clauses);
			free(new_pos_clauses);
			printf("fail to allocate memory\n");
			goto error;
		}
		s->variables[i].neg_clauses = new_neg_clauses;
		s->variables[i].pos_clauses = new_pos_clauses;
	}//realloc

	return s;
	
error:
	printf("fail to allocate memory for s\n");
	for (int j = 0; j <variables_number; j++) {
		if (s->variables != NULL && s->variables[j].neg_clauses != NULL) {
			free(s->variables[j].neg_clauses);
			s->variables[j].neg_clauses = NULL;
		}
		if (s->variables != NULL && s->variables[j].neg_clauses != NULL) {
			free(s->variables[j].pos_clauses);
			s->variables[j].pos_clauses = NULL;
		}
	}
	for (int i = 0; i < clause_number; i++) 
		if (s->clauses != NULL && s->clauses[i].literals != NULL) {
			free(s->clauses[i].literals);
			s->clauses[i].literals = NULL;
		}
	if (s->clauses != NULL)free(s->clauses);
	if (s->variables != NULL)free(s->variables);
	if (s->trail != NULL)free(s->trail);
	if (s->trail_level != NULL)free(s->trail_level);
	s->clauses = NULL;
	s->variables = NULL;
	s->trail = NULL;
	s->trail_level = NULL;
	free(s);
	s = NULL;
	return NULL;
}

void free_solver(solver*s,int clauses_number,int variables_number) {
	if (s == NULL)return;
	for (int j = 0; j < variables_number; j++) {
		if (s->variables != NULL && s->variables[j].neg_clauses != NULL) {
			free(s->variables[j].neg_clauses);
			s->variables[j].neg_clauses = NULL;
		}
		if (s->variables != NULL && s->variables[j].neg_clauses != NULL) {
			free(s->variables[j].pos_clauses);
			s->variables[j].pos_clauses = NULL;
		}
	}
	for (int i = 0; i < clauses_number; i++)
		if (s->clauses != NULL && s->clauses[i].literals != NULL) {
			free(s->clauses[i].literals);
			s->clauses[i].literals = NULL;
		}
	if (s->clauses != NULL)free(s->clauses);
	if (s->variables != NULL)free(s->variables);
	if (s->trail != NULL)free(s->trail);
	if (s->trail_level != NULL)free(s->trail_level);
	s->clauses = NULL;
	s->variables = NULL;
	s->trail = NULL;
	s->trail_level = NULL;
	free(s);
	s = NULL;
}

bool unit_propagation(solver* s);
void backtrack(solver* s);
bool all_satisfied(solver* s);
int select_variables(solver* s);
bool all_assigned(solver* s);
bool assign_new_variables(solver* s, int var, Assignment assign);

void decay_activities(solver* s) {
	s->var_increasement /= 0.95;  // 增量扩大，抵消衰减影响
}

bool dpll(solver* s) {
	if (!unit_propagation(s))return false;//apply unit_propagation 

	if (all_assigned(s)) return all_satisfied(s);// to check if all_assigned and if all assigned check if all satisfied

	int var = select_variables(s);      
	if (var == -1) return all_satisfied(s);//select a new variables

	decay_activities(s);

	if (!assign_new_variables(s, var, TRUE))return false;;
	if (dpll(s))return true;//make the variable TRUE and dpll

	backtrack(s);

	if(!assign_new_variables(s, var, FALSE))return false;
	if (dpll(s))return true;//make the variable FALSE and dpll

	backtrack(s);

	return false;//they're all false,and it means conlict
}


void bump_variable(solver*s,int var_idx) {
	s->variables[var_idx].activity += s->var_increasement;
	if (s->variables[var_idx].activity > 1e100) {
		for (int i = 0; i < s->var_count; i++) 
			s->variables[i].activity *= 1e-100;

		s->var_increasement *= 1e-100;
	}
}

bool unit_propagation(solver* s) {
	int trail_head = 0;
	while (trail_head < s->trail_size) {
		int var_idx = s->trail[trail_head] - 1;
		Variable* var = &s->variables[var_idx];

		// 获取当前变量赋值对应的子句列表（被证伪的文字所在的子句）
		Clause** clauses = (var->assignment == TRUE) ? var->neg_clauses : var->pos_clauses;
		int clause_count = (var->assignment == TRUE) ? var->neg_count : var->pos_count;
		bump_variable(s, var_idx);
		trail_head++; 

		for (int i = 0; i < clause_count; i++) {
			Clause* c = clauses[i];
			if (c->state) continue;  // 子句已满足，跳过

			// 确定哪个监视点被当前赋值证伪
			Literals l1 = c->literals[c->watch1];
			Literals l2 = c->literals[c->watch2];
			bool watch1_falsified = false;
			bool watch2_falsified = false;

			// 检查监视点1是否被证伪
			if (l1.value == s->trail[trail_head - 1]) {
				watch1_falsified = (var->assignment == TRUE && !l1.sign) ||
					(var->assignment == FALSE && l1.sign);
			}
			// 检查监视点2是否被证伪
			if (l2.value == s->trail[trail_head - 1]) {
				watch2_falsified = (var->assignment == TRUE && !l2.sign) ||
					(var->assignment == FALSE && l2.sign);
			}

			// 如果两个监视点都没被当前赋值影响，跳过
			if (!watch1_falsified && !watch2_falsified) continue;

			// 寻找新的监视点（未被证伪的文字）
			int new_watch = -1;
			for (unsigned int j = 0; j < c->size; j++) {
				if (j == c->watch1 || j == c->watch2) continue;

				Literals lit = c->literals[j];
				Variable* lit_var = &s->variables[lit.value - 1];

				// 未被证伪的条件：未赋值，或赋值与符号一致
				bool is_falsified = (lit_var->assignment == TRUE && !lit.sign) ||
					(lit_var->assignment == FALSE && lit.sign);
				if (!is_falsified) {
					new_watch = j;
					break;
				}
			}

			// 更新监视点
			if (new_watch != -1) {
				if (watch1_falsified) {
					c->watch1 = new_watch;
				}
				else if (watch2_falsified) {
					c->watch2 = new_watch;
				}
				continue;
			}

			// 未找到新监视点，检查剩余监视点状态
			Variable* v1 = &s->variables[l1.value - 1];
			Variable* v2 = &s->variables[l2.value - 1];

			bool l1_satisfied = (v1->assignment == TRUE && l1.sign) ||
				(v1->assignment == FALSE && !l1.sign);
			bool l2_satisfied = (v2->assignment == TRUE && l2.sign) ||
				(v2->assignment == FALSE && !l2.sign);

			if (l1_satisfied || l2_satisfied) {
				c->state = true;  // 子句已满足
				continue;
			}

			// 单位传播或冲突
			if (v1->assignment == UNSIGNNED) {
				// 对l1进行单位传播
				v1->assignment = l1.sign ? TRUE : FALSE;
				v1->decision_level = s->decision_level;
				s->trail[s->trail_size] = l1.value;
				s->trail_level[s->trail_size++] = s->decision_level;
			}
			else if (v2->assignment == UNSIGNNED) {
				// 对l2进行单位传播
				v2->assignment = l2.sign ? TRUE : FALSE;
				v2->decision_level = s->decision_level;
				s->trail[s->trail_size] = l2.value;
				s->trail_level[s->trail_size++] = s->decision_level;
			}
			else return false;
			
		}
	}
	return true;
}

void backtrack(solver* s) {
	s->decision_level -= 1;//didn't learn from conflict clauses

	if (s->decision_level < 0)printf("决策层为负\n");

	while (s->trail_size > 0 && s->trail_level[s->trail_size - 1] > s->decision_level) {
		int var = s->trail[--s->trail_size];
		if (var < 0 || var > s->var_count) {
			printf("在回溯backtrack中，var为无效下标\n");
			return;
		}//check the var

		s->variables[var - 1].assignment = UNSIGNNED;
		s->variables[var - 1].decision_level = -1;//init the assignment and the decision level
	}
}


bool all_satisfied(solver*s) {
	int var_count = s->var_count;
	int clause_count = s->clause_count;

	for (int clause_idx = 0; clause_idx < clause_count; clause_idx++) {
		bool stage = false;
		int size = s->clauses[clause_idx].size;
		int  value;
		bool sign;
		for (int i = 0; i < size; i++) {
			sign = s->clauses[clause_idx].literals[i].sign;
			value = s->clauses[clause_idx].literals[i].value;

			if ((s->variables[value - 1].assignment == TRUE && sign==true) || (s->variables[value - 1].assignment == FALSE && sign==false))
			{
				stage = true;
				break;
			}//check if it's satisfied
		}

		if (stage == false)return false;//if it's false means the clauses set are not all satisfied

	}
	return true;
}

int select_variables(solver*s) {
	int var = -1;
	int max_activity = 0;

	for (int i = 0; i < s->var_count; i++) 
			if (s->variables[i].assignment == UNSIGNNED&&s->variables[i].activity > max_activity) {
				max_activity = s->variables[i].activity;
				var = i + 1;
			}

	if (var == -1)for (int i = 0; i < s->var_count; i++) {
		if (s->variables[i].assignment == UNSIGNNED) {
			var = i + 1;
			break;
		}
	}

	if (var <= 0 || var > s->var_count) {
		printf("严重错误，挑选了无效的变量\n");
		return -2;
	}

	if (var == -1)printf("无法选择变量\n");

	return var;
}

bool all_assigned(solver* s) {
	bool all_assign = true;

	for (int i = 0; i < s->var_count; i++)if (s->variables[i].assignment == UNSIGNNED) {
		all_assign = false;
		break;
	}
	
	return all_assign;
}
bool assign_new_variables(solver* s, int var, Assignment assign) {
	s->decision_level++;
	//printf("选择变量 %d = %s 在决策级别 %d\n", var,assign==TRUE?"TRUE":"FALSE", s->decision_level);//主动挑选了一个变量赋值为TRUE，决策加一

	Variable* var_p = &s->variables[var - 1];
	var_p->assignment = assign;

	if (var_p->decision_level == -1)var_p->decision_level = s->decision_level;
	else {
		printf("出现了未知错误，未赋值的变量的决策层并不为初始值\n");
		return false;
	}

	s->trail[s->trail_size] = var;
	s->trail_level[s->trail_size++] = s->decision_level;
	if (s->trail_size < 0 || s->trail_size > s->var_count) goto trail_error;//to update the trail

	return true;

trail_error:
	printf("trail-size超出有效范围！\n");
	s->trail_size--;
	return false;
}

