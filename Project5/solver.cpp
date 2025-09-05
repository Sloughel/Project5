#include"stu.h"

void free_solver(solver* s, int clauses_number, int variables_number) {
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

solver* init_solver(FILE*input,int variables_number,int clause_number) {
	solver*s = (solver*)calloc(1,sizeof(solver));
	if (s == NULL)goto error;  //init s
	s->clauses = NULL;
	s->decision_level = 0;
	s->var_count = variables_number;
	s->clause_count = clause_number;
	s->assigned_num = 0;
	s->var_increasement = 1.0;//init variables under s

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
	free_solver(s,clause_number,variables_number);
	return NULL;
}



bool unit_propagation(solver* s);
void backtrack(solver* s,int level);
bool all_satisfied(solver* s);
int select_variables(solver* s);
bool all_assigned(solver* s);
bool assign_new_variables(solver* s, int var, Assignment assign);
void decay_activities(solver* s);

Clause* analyze_conflict(solver* s, Clause* conflict_clause) {  //learn from conflict clause,也就是说这是和单元传播原则配合起来运用的

	if (s == NULL || conflict_clause == NULL)return NULL;
	Literals* learned_literals = (Literals*)malloc(sizeof(Literals)*conflict_clause->size);
	if (learned_literals == NULL)return NULL;
	int learned_size = conflict_clause->size;//creat new leatned_literals

	memcpy(learned_literals, conflict_clause->literals, learned_size * sizeof(Literals));//copy the conflict clause

	int current_level = s->decision_level;
	int uip_count = 0;

	while (true) {

		uip_count = 0;
		Literals pivot;
		pivot.value = 0;
		pivot.sign = false;

		for (int i = 0; i < learned_size; i++) {
			int var_idx = learned_literals[i].value - 1;
			if (s->variables[var_idx].decision_level == current_level) {
				uip_count++;
				pivot = learned_literals[i];//find the decisions which are dicided in this decision level,and the last one is the point
			}
		}

		if (uip_count <= 1)break;

		for (int i = 0; i < learned_size; i++) 
			if (learned_literals[i].value == pivot.value && learned_literals[i].sign != pivot.sign) {  //去除枢纽节点的反文字
				learned_literals[i] = learned_literals[--learned_size];
				break;
			}

			Clause* reason = s->variables[pivot.value - 1].reason;
			if (reason == NULL)break;

			for (unsigned int i = 0; i < reason->size; i++) {
				Literals l = reason->literals[i];
				bool exist=false;
				for (int j = 0; j < learned_size; j++) {
					if (learned_literals[j].value == l.value && learned_literals[i].sign == l.sign) {
						exist = true;
						break;
					}
				}
				if (!exist) {
					learned_literals = (Literals*)realloc(learned_literals, (learned_size + 1) * sizeof(Literals));
					learned_literals[learned_size++] = l;
				}
			}
		
	}

	Clause* learned_clause = (Clause*)malloc(sizeof(Clause));
	learned_clause->literals = (Literals*)malloc(learned_size * sizeof(Literals));
	learned_clause->size = learned_size;
	learned_clause->is_learned = true;
	learned_clause->state = false;
	learned_clause->watch1 = 0;
	learned_clause->watch2 = (learned_size > 1) ? 1 : 0;
	memcpy(learned_clause->literals, learned_literals, learned_size*sizeof(Literals));
	free(learned_literals);

	return learned_clause;
}

bool handle_conflict(solver* s, Clause* conflict_clause) {
	if (s->decision_level == 0)return false;

	Clause* learned_clause = analyze_conflict(s, conflict_clause);
	if (learned_clause == NULL) return false;

	s->clauses = (Clause*)realloc(s->clauses, (s->clause_count + 1) * sizeof(Clause));
	if (s->clauses == NULL) {
		free(learned_clause->literals);
		free(learned_clause);
		return false;
	}
	s->clauses[s->clause_count] = *learned_clause;
	s->clause_count++;
	free(learned_clause); // 已复制，释放临时内存

	// 4. 计算回溯层级（学到的子句中最高的决策层 - 1）
	int backtrack_level = 0;
	for (unsigned int i = 0; i < learned_clause->size; i++) {
		int var_idx = learned_clause->literals[i].value - 1;
		int level = s->variables[var_idx].decision_level;
		if (level > backtrack_level && level < s->decision_level) {
			backtrack_level = level;
		}
	}

	// 5. 执行回溯
	backtrack(s,s->decision_level-backtrack_level); // 需要更改

	// 6. 对学到的子句执行单元传播（可能产生新的赋值）
	return unit_propagation(s);
	
}



bool dpll(solver* s) {
	if (!unit_propagation(s))return false;//apply unit_propagation 

	if (all_assigned(s)) return all_satisfied(s);// to check if all_assigned and if all assigned check if all satisfied

	int var = select_variables(s);      
	if (var == -1) return all_satisfied(s);//select a new variables
	
	decay_activities(s);

	if (!assign_new_variables(s, var, TRUE))return false;;
	s->assigned_num += 1;
	if (dpll(s))return true;//make the variable TRUE and dpll
	
	backtrack(s,1);

	if(!assign_new_variables(s, var, FALSE))return false;
	s->assigned_num += 1;
	if (dpll(s))return true;//make the variable FALSE and dpll

	backtrack(s,1);

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
static inline bool is_literal_falsified(Variable* var, bool sign) {
	return (var->assignment == TRUE && !sign) ||
		(var->assignment == FALSE && sign);
}
static inline bool is_literal_satisfied(Variable* var, bool sign) {
	return (var->assignment == TRUE && sign) ||
		(var->assignment == FALSE && !sign);
}

bool unit_propagation(solver* s) {
	int trail_head = 0;
	while (trail_head < s->trail_size) {

		int var_idx = s->trail[trail_head++] - 1;
		Variable* var = &s->variables[var_idx];//从历史轨迹中挑出赋值的变量

		
		Clause** clauses = (var->assignment == TRUE) ? var->neg_clauses : var->pos_clauses;
		int clause_count = (var->assignment == TRUE) ? var->neg_count : var->pos_count;//根据赋值情况寻找变量被证伪的子句

		bump_variable(s, var_idx);//bump the activity
		

		for (int i = 0; i < clause_count; i++) {
			Clause* c = clauses[i];//遍历证伪的子句集

			//if (c->state)
			//	continue;  //if satifyed,continue


		
			Literals l1 = c->literals[c->watch1];
			Literals l2 = c->literals[c->watch2];
			
			bool watch1_falsified = false;
			bool watch2_falsified = false;
			if (l1.value == var_idx + 1)
				watch1_falsified = is_literal_falsified(var, l1.sign);
			if (l2.value == var_idx + 1)
				watch2_falsified = is_literal_falsified(var, l2.sign);//看看两个监视文字是否有被证伪的
			

			
			if (!watch1_falsified && !watch2_falsified) continue;//若两者都满足则跳过

			
			int new_watch = -1;
			for (unsigned int j = 0; j < c->size; j++) {
				if (j == c->watch1 || j == c->watch2) continue;

				Literals lit = c->literals[j];
				Variable* lit_var = &s->variables[lit.value - 1];//在子句当中寻找新的监视文字

				if (lit_var->assignment == UNSIGNNED) {
					new_watch = j;
					break;
				}
				bool is_falsified = is_literal_falsified(lit_var, lit.sign);
				if (!is_falsified) {
					new_watch = j;
					break;//如果不是被证伪的，则可作为新的监视文字
				}
			}

			if (new_watch != -1) {
				if (watch1_falsified) 
					c->watch1 = new_watch;
				else if (watch2_falsified) 
					c->watch2 = new_watch;
				continue;
			}//如果找到了则替换

			
			Variable* v1 = &s->variables[l1.value - 1];
			Variable* v2 = &s->variables[l2.value - 1];

			bool l1_satisfied = is_literal_satisfied(v1, l1.sign);
			bool l2_satisfied = is_literal_satisfied(v2, l2.sign);

			if (l1_satisfied || l2_satisfied) {
				c->state = true;  
				continue;
			}//如果两个监视文字有一个满足，则说明子句满足

			
			if (v1->assignment == UNSIGNNED) {
				
				v1->assignment = l1.sign ? TRUE : FALSE;
				s->assigned_num++;
				v1->decision_level = s->decision_level;
				s->trail[s->trail_size] = l1.value;
				s->trail_level[s->trail_size++] = s->decision_level;
			}
			else if (v2->assignment == UNSIGNNED) {
				v2->assignment = l2.sign ? TRUE : FALSE;
				s->assigned_num++;
				v2->decision_level = s->decision_level;
				s->trail[s->trail_size] = l2.value;
				s->trail_level[s->trail_size++] = s->decision_level;
			}
			else return false;//要么有可以赋值的，要么说明冲突
			
		}
	}
	return true;
}

void backtrack(solver* s,int level) {
	s->decision_level -= level;//didn't learn from conflict clauses

	if (s->decision_level < 0)printf("决策层为负\n");

	while (s->trail_size > 0 && s->trail_level[s->trail_size - 1] > s->decision_level) {
		int var = s->trail[--s->trail_size];
		if (var < 0 || var > s->var_count) {
			printf("在回溯backtrack中，var为无效下标\n");
			return;
		}//check the var

		s->variables[var - 1].assignment = UNSIGNNED;
		s->variables[var - 1].decision_level = -1;//init the assignment and the decision level in variable
		s->assigned_num--;
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
	double max_activity = 0;

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
	return s->assigned_num==s->var_count;
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

void decay_activities(solver* s) {
	s->var_increasement /= 0.95;  // 增量扩大，抵消衰减影响
}

