#include "../include/mutator.h"

#include <assert.h>

#include <algorithm>
#include <cfloat>
#include <climits>
#include <cstdio>
#include <deque>
#include <fstream>

#include "../include/ast.h"
#include "../include/define.h"
#include "../include/utils.h"
#define _NON_REPLACE_

using namespace std;

static IR *empty_ir = new IR(kStringLiteral, "");

//#define GRAPHLOG

IR *Mutator::deep_copy_with_record(const IR *root, const IR *record) {
  IR *left = NULL, *right = NULL, *copy_res;

  if (root->left_) left = deep_copy_with_record(root->left_, record);
  if (root->right_) right = deep_copy_with_record(root->right_, record);

  if (root->op_ != NULL)
    copy_res =
        new IR(root->type_,
               OP3(root->op_->prefix_, root->op_->middle_, root->op_->suffix_),
               left, right, root->float_val_, root->str_val_, root->name_,
               root->mutated_times_, root->scope_, root->data_flag_);
  else
    copy_res = new IR(root->type_, NULL, left, right, root->float_val_,
                      root->str_val_, root->name_, root->mutated_times_,
                      root->scope_, root->data_flag_);

  copy_res->data_type_ = root->data_type_;

  if (root == record && record != NULL) {
    this->record_ = copy_res;
  }

  return copy_res;
}

vector<IR *> Mutator::mutate_all(vector<IR *> &v_ir_collector) {
  vector<IR *> res;
  IR *root = v_ir_collector[v_ir_collector.size() - 1];

  mutated_root_ = root;

  for (auto ir : v_ir_collector) {
    if (not_mutatable_types_.find(ir->type_) != not_mutatable_types_.end())
      continue;

    vector<IR *> v_mutated_ir = mutate(ir);

    for (auto i : v_mutated_ir) {
      IR *new_ir_tree = deep_copy_with_record(root, ir);
      replace(new_ir_tree, this->record_, i);

      extract_struct(new_ir_tree);
      string tmp = new_ir_tree->to_string();
      unsigned tmp_hash = hash(tmp);
      if (global_hash_.find(tmp_hash) != global_hash_.end()) {
        deep_delete(new_ir_tree);
        continue;
      }

      global_hash_.insert(tmp_hash);
      res.push_back(new_ir_tree);
    }
  }

  return res;
}

void Mutator::add_ir_to_library(IR *cur) {
  extract_struct(cur);
  cur = deep_copy(cur);
  add_ir_to_library_no_deepcopy(cur);
  return;
}

void Mutator::add_ir_to_library_no_deepcopy(IR *cur) {
  if (cur->left_) add_ir_to_library_no_deepcopy(cur->left_);
  if (cur->right_) add_ir_to_library_no_deepcopy(cur->right_);

  auto type = cur->type_;
  auto h = hash(cur);
  if (find(ir_library_hash_[type].begin(), ir_library_hash_[type].end(), h) !=
      ir_library_hash_[type].end())
    return;

  ir_library_hash_[type].insert(h);
  ir_library_[type].push_back(cur);

  return;
}

void Mutator::init_common_string(string filename) {
  common_string_library_.push_back("DO_NOT_BE_EMPTY");
  if (filename != "") {
    ifstream input_string(filename);
    string s;

    while (getline(input_string, s)) {
      common_string_library_.push_back(s);
    }
  }
}

void Mutator::init_data_library_2d(string filename) {
  ifstream input_file(filename);
  string s;

  cout << "[*] init data_library_2d: " << filename << endl;
  while (getline(input_file, s)) {
    vector<string> v_strbuf;
    auto prev_pos = -1;
    for (int i = 0; i < 3; i++) {
      auto pos = s.find(" ", prev_pos + 1);
      v_strbuf.push_back(s.substr(prev_pos + 1, pos - prev_pos - 1));
      prev_pos = pos;
    }
    v_strbuf.push_back(s.substr(prev_pos + 1, s.size() - prev_pos - 1));

    auto data_type1 = get_datatype_by_string(v_strbuf[0]);
    auto data_type2 = get_datatype_by_string(v_strbuf[2]);
    g_data_library_2d_[data_type1][v_strbuf[1]][data_type2].push_back(
        v_strbuf[3]);
  }

  return;
}

void Mutator::init_data_library(string filename) {
  ifstream input_file(filename);
  string s;

  cout << "[*] init data_library: " << filename << endl;
  while (getline(input_file, s)) {
    auto pos = s.find(" ");
    if (pos == string::npos) continue;
    auto data_type = get_datatype_by_string(s.substr(0, pos));
    auto v = s.substr(pos + 1, s.size() - pos - 1);
    g_data_library_[data_type].push_back(v);
  }

  return;
}

void Mutator::init_value_library() {
  vector<unsigned long> value_lib_init = {0,
                                          (unsigned long)LONG_MAX,
                                          (unsigned long)ULONG_MAX,
                                          (unsigned long)CHAR_BIT,
                                          (unsigned long)SCHAR_MIN,
                                          (unsigned long)SCHAR_MAX,
                                          (unsigned long)UCHAR_MAX,
                                          (unsigned long)CHAR_MIN,
                                          (unsigned long)CHAR_MAX,
                                          (unsigned long)MB_LEN_MAX,
                                          (unsigned long)SHRT_MIN,
                                          (unsigned long)INT_MIN,
                                          (unsigned long)INT_MAX,
                                          (unsigned long)SCHAR_MIN,
                                          (unsigned long)SCHAR_MIN,
                                          (unsigned long)UINT_MAX,
                                          (unsigned long)FLT_MAX,
                                          (unsigned long)DBL_MAX,
                                          (unsigned long)LDBL_MAX,
                                          (unsigned long)FLT_MIN,
                                          (unsigned long)DBL_MIN,
                                          (unsigned long)LDBL_MIN};

  value_library_.insert(value_library_.begin(), value_lib_init.begin(),
                        value_lib_init.end());

  return;
}

void Mutator::init_ir_library(string filename) {
  ifstream input_file(filename);
  string line;

  cout << "[*] init ir_library: " << filename << endl;
  while (getline(input_file, line)) {
    if (line.empty()) continue;
    auto p = parser(line);
    if (p == NULL) continue;

    vector<IR *> v_ir;
    auto res = p->translate(v_ir);
    p->deep_delete();
    p = NULL;

    add_ir_to_library(res);
    deep_delete(res);
  }
  return;
}

void Mutator::init_safe_generate_type(string filename) {
  ifstream input_file(filename);
  string line;

  cout << "[*] init safe generate type: " << filename << endl;
  while (getline(input_file, line)) {
    if (line.empty()) continue;
    auto node_type = get_nodetype_by_string("k" + line);
    safe_generate_type_.insert(node_type);
  }
}

void Mutator::init(string f_testcase, string f_common_string, string file2d,
                   string file1d, string f_gen_type) {
  if (!f_testcase.empty()) init_ir_library(f_testcase);

  // init value_library_
  init_value_library();

  // init common_string_library
  if (!f_common_string.empty()) init_common_string(f_common_string);

  // init data_library_2d
  if (!file2d.empty()) init_data_library_2d(file2d);

  if (!file1d.empty()) init_data_library(file1d);
  if (!f_gen_type.empty()) init_safe_generate_type(f_gen_type);

  float_types_.insert({kFloatLiteral});
  int_types_.insert(kIntLiteral);
  string_types_.insert({kStringLiteral, kIdentifier, kWindowName, kTriggerName, kConstraintName,
                        kViewName, kName});

  relationmap_[kDataColumnName][kDataTableName] = kRelationSubtype;
  relationmap_[kDataPragmaValue][kDataPragmaKey] = kRelationSubtype;
  relationmap_[kDataTableName][kDataTableName] = kRelationElement;
  relationmap_[kDataColumnName][kDataColumnName] = kRelationElement;

  split_stmt_types_.insert(kStmt);
  split_substmt_types_.insert({kStmt, kSelectClause, kSelectStmt});

#define MYSQLFUZZ
#ifdef MYSQLFUZZ
  not_mutatable_types_.insert(
      {kUnknown, kProgram, kStmtlist, kStmt, kCreateStmt, kDropStmt, kCreateTableStmt,
       kCreateIndexStmt, kCreateTriggerStmt, kCreateViewStmt, kDropIndexStmt,
       kDropTableStmt, kDropTriggerStmt, kDropViewStmt, kSelectStmt,
       kUpdateStmt, kInsertStmt, kAlterStmt});
#else
  not_mutatable_types_.insert({kUnknown, kProgram, kStmtlist, kStmt, kCreateStmt,
                               kDropStmt, kCreateTableStmt, kCreateIndexStmt,
                               kCreateViewStmt, kDropIndexStmt, kDropTableStmt,
                               kDropViewStmt, kSelectStmt, kUpdateStmt,
                               kInsertStmt, kAlterStmt, kReindexStmt});
#endif

  not_mutatable_types_.insert(float_types_.begin(), float_types_.end());
  not_mutatable_types_.insert(int_types_.begin(), int_types_.end());
  not_mutatable_types_.insert(string_types_.begin(), string_types_.end());
  return;
}

vector<IR *> Mutator::mutate(IR *input) {
  vector<IR *> res;

  if (!lucky_enough_to_be_mutated(input->mutated_times_)) {
    return res;
  }
  auto tmp = strategy_delete(input);
  if (tmp != NULL) {
    res.push_back(tmp);
  }

  tmp = strategy_insert(input);
  if (tmp != NULL) {
    res.push_back(tmp);
  }

  tmp = strategy_replace(input);
  if (tmp != NULL) {
    res.push_back(tmp);
  }

  input->mutated_times_ += res.size();
  for (auto i : res) {
    if (i == NULL) continue;
    i->mutated_times_ = input->mutated_times_;
  }
  return res;
}

bool Mutator::replace(IR *root, IR *old_ir, IR *new_ir) {
  auto parent_ir = locate_parent(root, old_ir);
  if (parent_ir == NULL) return false;
  if (parent_ir->left_ == old_ir) {
    deep_delete(old_ir);
    parent_ir->left_ = new_ir;
    return true;
  } else if (parent_ir->right_ == old_ir) {
    deep_delete(old_ir);
    parent_ir->right_ = new_ir;
    return true;
  }
  return false;
}

IR *Mutator::locate_parent(IR *root, IR *old_ir) {
  if (root->left_ == old_ir || root->right_ == old_ir) return root;

  if (root->left_ != NULL)
    if (auto res = locate_parent(root->left_, old_ir)) return res;
  if (root->right_ != NULL)
    if (auto res = locate_parent(root->right_, old_ir)) return res;

  return NULL;
}

IR *Mutator::strategy_delete(IR *cur) {
  assert(cur);
  MUTATESTART

  DOLEFT
  res = deep_copy(cur);
  if (res->left_ != NULL) deep_delete(res->left_);
  res->left_ = NULL;

  DORIGHT
  res = deep_copy(cur);
  if (res->right_ != NULL) deep_delete(res->right_);
  res->right_ = NULL;

  DOBOTH
  res = deep_copy(cur);
  if (res->left_ != NULL) deep_delete(res->left_);
  if (res->right_ != NULL) deep_delete(res->right_);
  res->left_ = res->right_ = NULL;

  MUTATEEND
}

IR *Mutator::strategy_insert(IR *cur) {
  assert(cur);

  auto res = deep_copy(cur);
  auto parent_type = cur->type_;

  if (res->right_ == NULL && res->left_ != NULL) {
    auto left_type = res->left_->type_;
    for (int k = 0; k < 4; k++) {
      auto fetch_ir = get_ir_from_library(parent_type);
      if (fetch_ir->left_ != NULL && fetch_ir->left_->type_ == left_type &&
          fetch_ir->right_ != NULL) {
        res->right_ = deep_copy(fetch_ir->right_);
        return res;
      }
    }
  } else if (res->right_ != NULL && res->left_ == NULL) {
    auto right_type = res->left_->type_;
    for (int k = 0; k < 4; k++) {
      auto fetch_ir = get_ir_from_library(parent_type);
      if (fetch_ir->right_ != NULL && fetch_ir->right_->type_ == right_type &&
          fetch_ir->left_ != NULL) {
        res->left_ = deep_copy(fetch_ir->left_);
        return res;
      }
    }
  } else if (res->left_ == NULL && res->right_ == NULL) {
    for (int k = 0; k < 4; k++) {
      auto fetch_ir = get_ir_from_library(parent_type);
      if (fetch_ir->right_ != NULL && fetch_ir->left_ != NULL) {
        res->left_ = deep_copy(fetch_ir->left_);
        res->right_ = deep_copy(fetch_ir->right_);
        return res;
      }
    }
  }

  return res;
}

IR *Mutator::strategy_replace(IR *cur) {
  assert(cur);

  MUTATESTART

  DOLEFT
  if (cur->left_ != NULL) {
    res = deep_copy(cur);

    auto new_node = get_ir_from_library(res->left_->type_);
    new_node->data_type_ = res->left_->data_type_;
    deep_delete(res->left_);
    res->left_ = deep_copy(new_node);
  }

  DORIGHT
  if (cur->right_ != NULL) {
    res = deep_copy(cur);

    auto new_node = get_ir_from_library(res->right_->type_);
    new_node->data_type_ = res->right_->data_type_;
    deep_delete(res->right_);
    res->right_ = deep_copy(new_node);
  }

  DOBOTH
  if (cur->left_ != NULL && cur->right_ != NULL) {
    res = deep_copy(cur);

    auto new_left = get_ir_from_library(res->left_->type_);
    auto new_right = get_ir_from_library(res->right_->type_);
    new_left->data_type_ = res->left_->data_type_;
    new_right->data_type_ = res->right_->data_type_;
    deep_delete(res->right_);
    res->right_ = deep_copy(new_right);

    deep_delete(res->left_);
    res->left_ = deep_copy(new_left);
  }

  MUTATEEND

  return res;
}

bool Mutator::lucky_enough_to_be_mutated(unsigned int mutated_times) {
  if (get_rand_int(mutated_times + 1) < LUCKY_NUMBER) {
    return true;
  }
  return false;
}

pair<string, string> Mutator::get_data_2d_by_type(DATATYPE type1,
                                                  DATATYPE type2) {
  pair<string, string> res("", "");
  auto size = data_library_2d_[type1].size();

  if (size == 0) return res;
  auto rint = get_rand_int(size);

  int counter = 0;
  for (auto &i : data_library_2d_[type1]) {
    if (counter++ == rint) {
      return std::make_pair(i.first, vector_rand_ele(i.second[type2]));
    }
  }
  return res;
}

IR *Mutator::generate_ir_by_type(IRTYPE type) {
  auto ast_node = generate_ast_node_by_type(type);
  ast_node->generate();
  vector<IR *> tmp_vector;
  ast_node->translate(tmp_vector);
  assert(tmp_vector.size());

  return tmp_vector[tmp_vector.size() - 1];
}

IR *Mutator::get_ir_from_library(IRTYPE type) {
  const int generate_prop = 1;
  const int threshold = 0;
#ifdef USEGENERATE
  if (ir_library_[type].empty() == true ||
      (get_rand_int(400) == 0 && type != kUnknown)) {
    auto ir = generate_ir_by_type(type);
    add_ir_to_library_no_deepcopy(ir);
    return ir;
  }
#endif
  if (ir_library_[type].empty()) return empty_ir;
  return vector_rand_ele(ir_library_[type]);
}

string Mutator::get_a_string() {
  unsigned com_size = common_string_library_.size();
  unsigned lib_size = string_library_.size();
  unsigned double_lib_size = lib_size * 2;

  unsigned rand_int = get_rand_int(double_lib_size + com_size);
  if (rand_int < double_lib_size) {
    return string_library_[rand_int >> 1];
  } else {
    rand_int -= double_lib_size;
    return common_string_library_[rand_int];
  }
}

unsigned long Mutator::get_a_val() {
  assert(value_library_.size());

  return vector_rand_ele(value_library_);
}

unsigned long Mutator::hash(string &sql) {
  return ducking_hash(sql.c_str(), sql.size());
}

unsigned long Mutator::hash(IR *root) {
  auto tmp_str = move(root->to_string());
  return this->hash(tmp_str);
}

void Mutator::debug(IR *root) {
  for (auto &i : data_library_[kDataFunctionName]) {
    cout << i << endl;
  }
}

Mutator::~Mutator() {}

void Mutator::extract_struct(IR *root) {
  static int counter = 0;
  auto type = root->type_;
  if (root->left_) {
    extract_struct(root->left_);
  }
  if (root->right_) {
    extract_struct(root->right_);
  }

  if (root->left_ || root->right_) return;

  if (root->data_type_ != kDataWhatever) {
    root->str_val_ = "x";
    return;
  }

  if (string_types_.find(type) != string_types_.end()) {
    root->str_val_ = "'x'";
  } else if (int_types_.find(type) != int_types_.end()) {
    root->int_val_ = 1;
  } else if (float_types_.find(type) != float_types_.end()) {
    root->float_val_ = 1.0;
  }
}

void Mutator::extract_struct2(IR *root) {
  static int counter = 0;
  auto type = root->type_;
  if (root->left_) {
    extract_struct2(root->left_);
  }
  if (root->right_) {
    extract_struct2(root->right_);
  }

  if (root->left_ || root->right_) return;

  if (root->data_type_ != kDataWhatever) {
    root->str_val_ = "x" + to_string(counter++);
    return;
  }

  if (string_types_.find(type) != string_types_.end()) {
    root->str_val_ = "'x'";
  } else if (int_types_.find(type) != int_types_.end()) {
    root->int_val_ = 1;
  } else if (float_types_.find(type) != float_types_.end()) {
    root->float_val_ = 1.0;
  }
}

void Mutator::reset_data_library() {
  data_library_.clear();
  data_library_2d_.clear();
}

string Mutator::parse_data(string &input) {
  string res;
  if (!input.compare("_int_")) {
    res = to_string(get_a_val());
  } else if (!input.compare("_empty_")) {
    res = "";
  } else if (!input.compare("_boolean_")) {
    if (get_rand_int(2) == 0)
      res = "false";
    else
      res = "true";
  } else if (!input.compare("_string_")) {
    res = get_a_string();
  } else {
    res = input;
  }

  return res;
}

bool Mutator::validate(IR *&root) {
  reset_data_library();
  string sql = root->to_string();
  auto ast = parser(sql);
  if (ast == NULL) return false;

  deep_delete(root);
  root = NULL;

  vector<IR *> ir_vector;
  ast->translate(ir_vector);
  ast->deep_delete();

  root = ir_vector[ir_vector.size() - 1];
  reset_id_counter();

  if (fix(root) == false) {
    return false;
  }

  return true;
}

unsigned int Mutator::calc_node(IR *root) {
  unsigned int res = 0;
  if (root->left_) res += calc_node(root->left_);
  if (root->right_) res += calc_node(root->right_);

  return res + 1;
}

bool Mutator::fix(IR *root) {
  map<IR **, IR *> m_save;
  bool res = true;

  auto stmts = split_to_stmt(root, m_save, split_stmt_types_);

  if (stmts.size() > 8) {
    connect_back(m_save);
    return false;
  }

  clear_scope_library(true);
  for (auto &stmt : stmts) {
    map<IR **, IR *> m_substmt_save;
    auto substmts = split_to_stmt(stmt, m_substmt_save, split_substmt_types_);

    int stmt_num = substmts.size();
    if (stmt_num > 4) {
      connect_back(m_save);
      connect_back(m_substmt_save);
      return false;
    }
    for (auto &substmt : substmts) {
      clear_scope_library(false);
      int tmp_node_num = calc_node(substmt);
      if ((stmt_num == 1 && tmp_node_num > 150) || tmp_node_num > 120) {
        connect_back(m_save);
        connect_back(m_substmt_save);
        return false;
      }
      res = fix_one(substmt, scope_library_) && res;

      if (res == false) {
        connect_back(m_save);
        connect_back(m_substmt_save);
        return false;
      }
    }
    res = connect_back(m_substmt_save) && res;
  }
  res = connect_back(m_save) && res;

  return res;
}

vector<IR *> Mutator::split_to_stmt(IR *root, map<IR **, IR *> &m_save,
                                    set<IRTYPE> &split_set) {
  vector<IR *> res;
  deque<IR *> bfs = {root};

  while (!bfs.empty()) {
    auto node = bfs.front();
    bfs.pop_front();

    if (node && node->left_) bfs.push_back(node->left_);
    if (node && node->right_) bfs.push_back(node->right_);

    if (node->left_ && find(split_set.begin(), split_set.end(),
                            node->left_->type_) != split_set.end()) {
      res.push_back(node->left_);
      m_save[&node->left_] = node->left_;
      node->left_ = NULL;
    }
    if (node->right_ && find(split_set.begin(), split_set.end(),
                             node->right_->type_) != split_set.end()) {
      res.push_back(node->right_);
      m_save[&node->right_] = node->right_;
      node->right_ = NULL;
    }
  }

  if (find(split_set.begin(), split_set.end(), root->type_) != split_set.end())
    res.push_back(root);

  return res;
}

bool Mutator::connect_back(map<IR **, IR *> &m_save) {
  for (auto &iter : m_save) {
    *(iter.first) = iter.second;
  }
  return true;
}

static set<IR *> visited;

bool Mutator::fix_one(IR *stmt_root,
                      map<int, map<DATATYPE, vector<IR *>>> &scope_library) {
  visited.clear();
  analyze_scope(stmt_root);
  auto graph = build_graph(stmt_root, scope_library);

#ifdef GRAPHLOG
  for (auto &iter : graph) {
    cout << "Node: " << iter.first->to_string() << " connected with:" << endl;
    for (auto &k : iter.second) {
      cout << k->to_string() << endl;
    }
    cout << "--------" << endl;
  }
  cout << "OUTPUT END" << endl;
#endif
  return fill_stmt_graph(graph);
}

void Mutator::analyze_scope(IR *stmt_root) {
  if (stmt_root->left_) {
    analyze_scope(stmt_root->left_);
  }
  if (stmt_root->right_) {
    analyze_scope(stmt_root->right_);
  }

  auto data_type = stmt_root->data_type_;
  if (data_type == kDataWhatever) return;

  scope_library_[stmt_root->scope_][data_type].push_back(stmt_root);
}

map<IR *, vector<IR *>> Mutator::build_graph(
    IR *stmt_root, map<int, map<DATATYPE, vector<IR *>>> &scope_library) {
  map<IR *, vector<IR *>> res;
  deque<IR *> bfs = {stmt_root};

  while (!bfs.empty()) {
    auto node = bfs.front();
    bfs.pop_front();

    auto cur_scope = node->scope_;
    auto cur_data_flag = node->data_flag_;
    auto cur_data_type = node->data_type_;

    if (find(int_types_.begin(), int_types_.end(), node->type_) !=
        int_types_.end()) {
      if (get_rand_int(100) > 50)
        node->int_val_ = vector_rand_ele(value_library_);
      else
        node->int_val_ = get_rand_int(100);
    } else if (find(float_types_.begin(), float_types_.end(), node->type_) !=
               float_types_.end()) {
      node->float_val_ = (double)(get_rand_int(100000000));
    }

    if (node->left_) bfs.push_back(node->left_);
    if (node->right_) bfs.push_back(node->right_);
    if (cur_data_type == kDataWhatever) continue;

    res[node];
    cur_scope--;

    if (relationmap_.find(cur_data_type) != relationmap_.end()) {
      auto &target_data_type_map = relationmap_[cur_data_type];
      for (auto &target : target_data_type_map) {
        IR *pick_node = NULL;
        if (isMapToClosestOne(cur_data_flag)) {
          pick_node = find_closest_node(stmt_root, node, target.first);
          if (pick_node && pick_node->scope_ != cur_scope) {
            pick_node = NULL;
          }
        } else {
          if (!node->str_val_.empty()) {
          }

          if (!isDefine(cur_data_flag) ||
              relationmap_[cur_data_type][target.first] != kRelationElement) {
            if (!scope_library[cur_scope][target.first].empty())
              pick_node =
                  vector_rand_ele(scope_library[cur_scope][target.first]);
          }
        }
        if (pick_node != NULL) res[pick_node].push_back(node);
      }
    }
  }

  return res;
}

bool Mutator::fill_stmt_graph(map<IR *, vector<IR *>> &graph) {
  bool res = true;
  map<IR *, bool> zero_indegrees;
  for (auto &iter : graph) {
    if (zero_indegrees.find(iter.first) == zero_indegrees.end()) {
      zero_indegrees[iter.first] = true;
    }
    for (auto ir : iter.second) {
      zero_indegrees[ir] = false;
    }
  }
  for (auto &iter : graph) {
    auto type1 = iter.first->data_type_;
    auto beg = iter.first;
    if (zero_indegrees[beg] == false || visited.find(beg) != visited.end()) {
      continue;
    }
    res &= fill_one(iter.first);
    res &= fill_stmt_graph_one(graph, iter.first);
  }

  return res;
}

bool Mutator::fill_stmt_graph_one(map<IR *, vector<IR *>> &graph, IR *ir) {
  if (graph.find(ir) == graph.end()) return true;

  bool res = true;
  auto type = ir->data_type_;
  auto &vec = graph[ir];

  if (!vec.empty()) {
    for (auto d : vec) {
      res = res & fill_one_pair(ir, d);
      res = res & fill_stmt_graph_one(graph, d);
    }
  }
  return res;
}

static bool replace_in_vector(string &old_str, string &new_str,
                              vector<string> &victim) {
  for (int i = 0; i < victim.size(); i++) {
    if (victim[i] == old_str) {
      victim[i] = new_str;
      return true;
    }
  }
  return false;
}

static bool remove_in_vector(string &str_to_remove, vector<string> &victim) {
  for (auto iter = victim.begin(); iter != victim.end(); iter++) {
    if (*iter == str_to_remove) {
      victim.erase(iter);
      return true;
    }
  }
  return false;
}

bool Mutator::remove_one_from_datalibrary(DATATYPE datatype, string &key) {
  return remove_in_vector(key, data_library_[datatype]);
}

bool Mutator::replace_one_from_datalibrary(DATATYPE datatype, string &old_str,
                                           string &new_str) {
  return replace_in_vector(old_str, new_str, data_library_[datatype]);
}

bool Mutator::remove_one_pair_from_datalibrary_2d(DATATYPE p_datatype,
                                                  DATATYPE c_data_type,
                                                  string &p_key) {
  for (auto &value : data_library_2d_[p_datatype][p_key][c_data_type]) {
    remove_one_from_datalibrary(c_data_type, value);
  }

  data_library_2d_[p_datatype][p_key].erase(c_data_type);
  if (data_library_2d_[p_datatype][p_key].empty()) {
    remove_one_from_datalibrary(p_datatype, p_key);
    data_library_2d_[p_datatype].erase(p_key);
  }

  return true;
}

#define has_element(a, b) (find(a.begin(), a.end(), b) != (a).end())
#define has_key(a, b) ((a).find(b) != (a).end())

bool Mutator::replace_one_value_from_datalibray_2d(DATATYPE p_datatype,
                                                   DATATYPE c_data_type,
                                                   string &p_key,
                                                   string &old_c_value,
                                                   string &new_c_value) {
  replace_one_from_datalibrary(c_data_type, old_c_value, new_c_value);
  replace_in_vector(old_c_value, new_c_value,
                    data_library_2d_[p_datatype][p_key][c_data_type]);
  return true;
}

bool Mutator::fill_one(IR *ir) {
  auto type = ir->data_type_;
  visited.insert(ir);
  if (isDefine(ir->data_flag_)) {
    string new_name = gen_id_name();
    data_library_[type].push_back(new_name);
    ir->str_val_ = new_name;

    for (auto iter : relationmap_) {
      for (auto iter2 : iter.second) {
        if (iter2.first == type && iter2.second == kRelationSubtype) {
          data_library_2d_[type][new_name];
        }
      }
    }
    return true;
  } else if (isAlias(ir->data_flag_)) {
    string alias_target;
    if (data_library_[type].size() != 0)
      alias_target = vector_rand_ele(data_library_[type]);
    else {
      alias_target = get_rand_int(2) ? "v0" : "v1";
    }

    string new_name = gen_id_name();
    data_library_[type].push_back(new_name);
    ir->str_val_ = new_name;

    if (has_key(data_library_2d_, type)) {
      if (has_key(data_library_2d_[type], alias_target)) {
        data_library_2d_[type][new_name] = data_library_2d_[type][alias_target];
      }
    }
    return true;
  }

  else if (data_library_.find(type) != data_library_.end()) {
    if (data_library_[type].empty()) {
      ir->str_val_ = "v0";
      return false;
    }
    ir->str_val_ = vector_rand_ele(data_library_[type]);
    if (isUndefine(ir->data_flag_)) {
      remove_one_from_datalibrary(ir->data_type_, ir->str_val_);
      if (has_key(data_library_2d_, type) &&
          has_key(data_library_2d_[type], ir->str_val_)) {
        for (auto itr = data_library_2d_[type][ir->str_val_].begin();
             has_key(data_library_2d_[type], ir->str_val_) &&
             itr != data_library_2d_[type][ir->str_val_].end();
             itr++) {
          auto c_data_type = *itr;
          remove_one_pair_from_datalibrary_2d(type, c_data_type.first,
                                              ir->str_val_);
          if (!has_key(data_library_2d_[type], ir->str_val_)) break;
          itr--;
        }
      }
    }
    return true;
  } else if (g_data_library_.find(type) != g_data_library_.end()) {
    if (g_data_library_[type].empty()) {
      return false;
    }
    ir->str_val_ = vector_rand_ele(g_data_library_[type]);
    return true;
  } else if (g_data_library_2d_.find(type) != g_data_library_2d_.end()) {
    int choice = get_rand_int(g_data_library_2d_[type].size());
    auto iter = g_data_library_2d_[type].begin();
    while (choice > 0) {
      iter++;
      choice--;
    }
    ir->str_val_ = iter->first;
    return true;
  } else {
    return false;
  }
  return true;
}

bool Mutator::fill_one_pair(IR *parent, IR *child) {
  visited.insert(child);

  bool is_define = isDefine(child->data_flag_);
  bool is_replace = isReplace(child->data_flag_);
  bool is_undefine = isUndefine(child->data_flag_);
  bool is_alias = isAlias(child->data_flag_);

  string new_name = "";
  if (is_define || is_replace || is_alias) {
    new_name = gen_id_name();
  }

  auto p_type = parent->data_type_;
  auto c_type = child->data_type_;
  auto p_str = parent->str_val_;

  auto r_type = relationmap_[c_type][p_type];
  switch (r_type) {
    case kRelationElement:

      if (is_replace) {
        child->str_val_ = new_name;
        replace_one_from_datalibrary(c_type, p_str, new_name);

        if (has_key(data_library_2d_, p_type)) {
          if (has_key(data_library_2d_[p_type], p_str)) {
            auto tmp = data_library_2d_[p_type].extract(p_str);
            tmp.key() = new_name;
            data_library_2d_[p_type].insert(move(tmp));
          }
        } else {
          for (auto &i1 : data_library_2d_) {
            for (auto &i2 : i1.second) {
              for (auto &i3 : i2.second) {
                if (i3.first == c_type) {
                  if (has_element(i3.second, p_str)) {
                    replace_in_vector(p_str, new_name, i3.second);
                    goto END;
                  }
                }
              }
            }
          }
        }
      } else if (is_alias) {
        child->str_val_ = new_name;

        if (has_key(data_library_2d_, p_type)) {
          if (has_key(data_library_2d_[p_type], p_str)) {
            data_library_2d_[p_type][new_name] =
                data_library_2d_[p_type][p_str];
            data_library_[p_type].push_back(new_name);
          }
        }
      } else {
        child->str_val_ = p_str;
      }
    END:
      break;

    case kRelationSubtype:
      if (data_library_2d_.find(p_type) != data_library_2d_.end()) {
        if (data_library_2d_[p_type].find(p_str) !=
            data_library_2d_[p_type].end()) {
          if (is_define) {
            data_library_2d_[p_type][p_str][c_type].push_back(new_name);
            child->str_val_ = new_name;
            data_library_[c_type].push_back(new_name);
            break;
          } else if (is_undefine) {
            if ((data_library_2d_[p_type][p_str][c_type]).empty()) {
              child->str_val_ = "v1";
              break;
            }
            child->str_val_ =
                vector_rand_ele(data_library_2d_[p_type][p_str][c_type]);
            remove_in_vector(child->str_val_,
                             data_library_2d_[p_type][p_str][c_type]);
            remove_in_vector(child->str_val_, data_library_[c_type]);
            break;
          } else if (data_library_2d_[p_type][p_str].find(c_type) !=
                     data_library_2d_[p_type][p_str].end()) {
            if (data_library_2d_[p_type][p_str][c_type].empty() == false) {
              child->str_val_ =
                  vector_rand_ele(data_library_2d_[p_type][p_str][c_type]);
            }
          } else {
            if (data_library_[c_type].empty()) {
              if (get_rand_int(2) == 1) {
                child->str_val_ = "v0";
              } else {
                child->str_val_ = "v1";
              }
            } else
              child->str_val_ = vector_rand_ele(data_library_[c_type]);
          }
        } else {
        }
      } else if (g_data_library_2d_.find(p_type) != g_data_library_2d_.end()) {
        if (g_data_library_2d_[p_type].find(p_str) !=
            g_data_library_2d_[p_type].end()) {
          if (g_data_library_2d_[p_type][p_str].find(c_type) !=
              g_data_library_2d_[p_type][p_str].end()) {
            if (g_data_library_2d_[p_type][p_str][c_type].empty() == false) {
              child->str_val_ =
                  vector_rand_ele(g_data_library_2d_[p_type][p_str][c_type]);
            }
          }
        }
      } else {
        return false;
      }

      break;

    default:
      assert(0);
      break;
  }

  return true;
}

void Mutator::clear_scope_library(bool clear_define) {
  int level = clear_define ? 0 : 1;
  int sz = scope_library_.size();
  scope_library_.clear();

  return;
}

static IR *search_mapped_ir(IR *ir, DATATYPE type) {
  vector<IR *> to_search;
  vector<IR *> backup;
  to_search.push_back(ir);
  while (!to_search.empty()) {
    for (auto i : to_search) {
      if (i->data_type_ == type) {
        return i;
      }
      if (i->left_) {
        backup.push_back(i->left_);
      }
      if (i->right_) {
        backup.push_back(i->right_);
      }
    }
    to_search = move(backup);
    backup.clear();
  }
  return NULL;
}

IR *Mutator::find_closest_node(IR *stmt_root, IR *node, DATATYPE type) {
  auto cur = node;
  while (true) {
    auto parent = locate_parent(stmt_root, cur);
    if (!parent) break;
    bool flag = false;
    while (parent->left_ == NULL || parent->right_ == NULL) {
      cur = parent;
      parent = locate_parent(stmt_root, cur);
      if (!parent) {
        flag = true;
        break;
      }
    }
    if (flag) return NULL;

    auto search_root = parent->left_ == cur ? parent->right_ : parent->left_;
    auto res = search_mapped_ir(search_root, type);
    if (res) return res;

    cur = parent;
  }
  return NULL;
}

int Mutator::try_fix(char *buf, int len, char *&new_buf, int &new_len) {
  string sql(buf);
  auto ast = parser(sql);

  new_buf = buf;
  new_len = len;
  if (ast == NULL) return 0;

  vector<IR *> v_ir;
  auto ir_root = ast->translate(v_ir);
  ast->deep_delete();

  if (ir_root == NULL) return 0;
  bool fixed_result = validate(ir_root);
  string fixed;
  if (fixed_result != false) {
    fixed = ir_root->to_string();
  }
  deep_delete(ir_root);
  if (fixed.empty()) return 0;

  char *sfixed = (char *)malloc(fixed.size() + 1);
  memcpy(sfixed, fixed.c_str(), fixed.size());
  sfixed[fixed.size()] = 0;

  new_buf = sfixed;
  new_len = fixed.size();

  return 1;
}

vector<IR *> Mutator::strategy_replace_left_with_kUnknown(IR *cur) {
  vector<IR *> res;
  int depth = 1;
  while(1) {
    IR *cur_copy = deep_copy(cur);
    IR *p = cur_copy->left_;
    int depth_counter = depth;
    while(--depth_counter) p = p->left_;
    if (p->type_ != kUnknown) {
      deep_delete(cur_copy);
      break;
    }
    auto new_node = get_ir_from_library(p->right_->type_);
    if (new_node != empty_ir) {
      new_node->data_type_ = p->right_->data_type_;
      deep_delete(p->right_);
      p->right_ = deep_copy(new_node);
      res.push_back(cur_copy);
    } else {
      deep_delete(cur_copy);
    }
    ++depth;
  }

  IR *cur_copy = deep_copy(cur);
  IR *p = cur_copy;
  while(p->left_->type_ == kUnknown) p = p->left_;
  auto new_node = get_ir_from_library(p->left_->type_);
  if (new_node != empty_ir) {
    new_node->data_type_ = p->left_->data_type_;
    deep_delete(p->left_);
    p->left_ = deep_copy(new_node);
    res.push_back(cur_copy);
  }
  return res;
}

vector<IR *> Mutator::strategy_replace_left(IR *cur) {
  vector<IR *> res;
  if (cur->left_ != NULL)
    if (cur->left_->type_ != kUnknown) {
      auto new_node = get_ir_from_library(cur->left_->type_);
      if (new_node != empty_ir) {
        auto cur_copy = deep_copy(cur);
        new_node->data_type_ = cur_copy->left_->data_type_;
        deep_delete(cur_copy->left_);
        cur_copy->left_ = deep_copy(new_node);
        res.push_back(cur_copy);
      }
    } else {
      // cur->left_->type_ == kUnknown
      res = strategy_replace_left_with_kUnknown(cur);
    }
  return res;
}

vector<IR *> Mutator::strategy_replace_right(IR *cur) {
  vector<IR *> res;
  if (cur->right_ != NULL) {
    auto new_node = get_ir_from_library(cur->right_->type_);
    if (new_node != empty_ir) {
      auto cur_copy = deep_copy(cur);
      new_node->data_type_ = cur_copy->right_->data_type_;
      deep_delete(cur_copy->right_);
      cur_copy->right_ = deep_copy(new_node);
      res.push_back(cur_copy);
    }
  }
  return res;
}

vector<IR *> Mutator::mutate2(IR *input) {
  /*
  kProgram, kStmtlist, kStmt, kCreateStmt, kDropStmt, kCreateTableStmt,
  kCreateIndexStmt, kCreateTriggerStmt, kCreateViewStmt, kDropIndexStmt,
  kDropTableStmt, kDropTriggerStmt, kDropViewStmt, kSelectStmt,
  kUpdateStmt, kInsertStmt, kAlterStmt, kUnknown

  kFloatLiteral

  kIntLiteral

  kStringLiteral, kIdentifier, kWindowName, kTriggerName, kConstraintName,
  kViewName, kName
  */
  vector<IR *> res;

  if (!lucky_enough_to_be_mutated(input->mutated_times_)) {
    return res;
  }

  // All nodes are replaced
  vector<IR *> tmp_vec = strategy_replace_left(input);
  if (tmp_vec.size()) res.insert(res.end(), tmp_vec.begin(), tmp_vec.end());
  tmp_vec = strategy_replace_right(input);
  if (tmp_vec.size()) res.insert(res.end(), tmp_vec.begin(), tmp_vec.end());

  switch (input->type_) {
    case kSelectWithParens: {
      /*
      OP_LP select_no_parens OP_RP
      OP_LP select_with_parens OP_RP
      */
      if (input->left_->type_ != kSelectNoParens) {
        auto select_no_parens_node = get_ir_from_library(kSelectNoParens);
        if (select_no_parens_node != empty_ir) {
          auto copy = deep_copy(input);
          deep_delete(copy->left_);
          copy->left_ = deep_copy(select_no_parens_node);
          res.push_back(copy);
        }
      }
      if (input->left_->type_ != kSelectWithParens) {
        auto select_with_parens_node = get_ir_from_library(kSelectWithParens);
        if (select_with_parens_node != empty_ir) {
          auto copy = deep_copy(input);
          deep_delete(copy->left_);
          copy->left_ = deep_copy(select_with_parens_node);
          res.push_back(copy);
        }
      }
      break;
    }
    case kSelectNoParens:
      /*
      opt_with_clause select_clause_list opt_order_clause opt_limit_clause
      */
      break;
    case kSelectClauseList: {
      /*
      select_clause
      select_clause combine_clause select_clause_list
      */
      if (input->right_ == NULL) {
        auto select_clause_node = input->left_;
        auto combine_clause_node = get_ir_from_library(kCombineClause);
        auto select_clause_list_node = get_ir_from_library(kSelectClauseList);
        if (combine_clause_node != empty_ir && select_clause_list_node != empty_ir) {
          auto tmp = new IR(kUnknown, OP3("", "", ""), deep_copy(select_clause_node), deep_copy(combine_clause_node));
          tmp = new IR(input, tmp, deep_copy(select_clause_list_node));
          tmp->operand_num_ = 2;
          res.push_back(tmp);
        }
      } else {
        auto select_clause_node = input->left_->left_;
        auto tmp = new IR(input, deep_copy(select_clause_node), NULL);
        tmp->operand_num_ = 1;
        res.push_back(tmp);
      }
      break;
    }
    case kSelectClause:
      /*
      SELECT opt_all_or_distinct select_target opt_from_clause opt_where_clause opt_group_clause opt_window_clause
      */
      break;
    case kCombineClause: {
      /*
      UNION
      INTERSECT
      EXCEPT
      */
      if (input->op_->prefix_ != "UNION") {
        auto copy = deep_copy(input);
        copy->op_->prefix_ = "UNION";
        res.push_back(copy);
      }
      if (input->op_->prefix_ != "INTERSECT") {
        auto copy = deep_copy(input);
        copy->op_->prefix_ = "INTERSECT";
        res.push_back(copy);
      }
      if (input->op_->prefix_ != "EXCEPT") {
        auto copy = deep_copy(input);
        copy->op_->prefix_ = "EXCEPT";
        res.push_back(copy);
      }
      break;
    }
    case kOptFromClause: {
      /*
      from_clause
      (null)
      */
      if (input->left_ != NULL)
        res.push_back(new IR(kOptFromClause, string("")));
      else {
        auto from_clause_node = get_ir_from_library(kFromClause);
        if (from_clause_node != empty_ir) {
          auto tmp = new IR(kOptFromClause, OP3("", "", ""), deep_copy(from_clause_node));
          res.push_back(tmp);
        }
      }
      break;
    }
    case kSelectTarget:
      /*
      expr_list
      */
      break;
    case kOptWindowClause: {
      /*
      window_clause
      (null)
      */
      if (input->left_ != NULL)
        res.push_back(new IR(kOptWindowClause, string("")));
      else {
        auto window_clause_node = get_ir_from_library(kWindowClause);
        if (window_clause_node != empty_ir) {
          auto tmp = new IR(kOptWindowClause, OP3("", "", ""), deep_copy(window_clause_node));
          res.push_back(tmp);
        }
      }
      break;
    }
    case kWindowClause:
      /*
      WINDOW window_def_list
      */
      break;
    case kWindowDefList: {
      /*
      window_def
      window_def OP_COMMA window_def_list
      */
      if (input->right_ == NULL) {
        auto window_def_list_node = get_ir_from_library(kWindowDefList);
        if (window_def_list_node != empty_ir) {
          auto tmp = new IR(input, deep_copy(input->left_), deep_copy(window_def_list_node));
          tmp->operand_num_ = 2;
          tmp->op_->middle_ = ",";
          res.push_back(tmp);
        }
      } else {
        auto copy = deep_copy(input);
        deep_delete(copy->right_);
        copy->right_ = NULL;
        copy->operand_num_ = 1;
        copy->op_->middle_ = "";
        res.push_back(copy);
      }
      break;
    }
    case kWindowDef: {
      /*
      window_name AS OP_LP window OP_RP (window_name is not mutated)
      */
      for (auto node : res) {
        auto identifier_node = node->left_->left_;
        identifier_node->data_type_ = kDataWindowName;
        identifier_node->scope_ = 1;
        identifier_node->data_flag_ = kDefine;
      }
      break;
    }
    case kWindow:
      /*
      opt_exist_window_name opt_partition opt_order_clause opt_frame_clause
      */
      break;
    case kOptPartition: {
      /*
      PARTITION BY expr_list
      (null)
      */
      if (input->left_ != NULL)
        res.push_back(new IR(kOptPartition, string("")));
      else {
        auto expr_list_node = get_ir_from_library(kExprList);
        if (expr_list_node != empty_ir) {
          auto tmp = new IR(kOptPartition, OP3("PARTITION BY", "", ""), deep_copy(expr_list_node));
          res.push_back(tmp);
        }
      }
      break;
    }
    case kOptFrameClause: {
      /*
      range_or_rows frame_bound_start
      range_or_rows BETWEEN frame_bound_start AND frame_bound_end
      (null)
      */
      if (input->left_ != NULL) {
        res.push_back(new IR(kOptFrameClause, string("")));
        if (input->left_->type_ != kUnknown) {
          auto frame_bound_end_node = get_ir_from_library(kFrameBoundEnd);
          if (frame_bound_end_node != empty_ir) {
            auto tmp = deep_copy(input);
            tmp->type_ = kUnknown;
            tmp->op_->middle_ = "BETWEEN";
            tmp->op_->suffix_ = "AND";
            tmp = new IR(input, tmp, deep_copy(frame_bound_end_node));
            res.push_back(tmp);
          }
        } else {
          auto range_or_rows_node = input->left_->left_;
          auto frame_bound_start_node = input->left_->right_;
          auto tmp = new IR(input, deep_copy(range_or_rows_node), deep_copy(frame_bound_start_node));
          res.push_back(tmp);
        }
      } else {
        auto range_or_rows_node = get_ir_from_library(kRangeOrRows);
        auto frame_bound_start_node = get_ir_from_library(kFrameBoundStart);
        auto frame_bound_end_node = get_ir_from_library(kFrameBoundEnd);
        if (range_or_rows_node != empty_ir && frame_bound_start_node != empty_ir) {
          auto tmp = new IR(kOptFrameClause, OP3("", "", ""), deep_copy(range_or_rows_node), deep_copy(frame_bound_start_node));
          res.push_back(tmp);
          if (frame_bound_end_node != empty_ir) {
            auto tmp = new IR(kUnknown, OP3("", "BETWEEN", "AND"), deep_copy(get_ir_from_library(kRangeOrRows)), deep_copy(get_ir_from_library(kFrameBoundStart)));
            tmp = new IR(kOptFrameClause, OP3("", "", ""), tmp, deep_copy(frame_bound_end_node));
            res.push_back(tmp);
          }
        }
      }
      break;
    }
    case kRangeOrRows: {
      /*
      RANGE
      ROWS
      GROUPS
      */
      if (input->op_->prefix_ != "RANGE") {
        auto copy = deep_copy(input);
        copy->op_->prefix_ = "RANGE";
        res.push_back(copy);
      }
      if (input->op_->prefix_ != "ROWS") {
        auto copy = deep_copy(input);
        copy->op_->prefix_ = "ROWS";
        res.push_back(copy);
      }
      if (input->op_->prefix_ != "GROUPS") {
        auto copy = deep_copy(input);
        copy->op_->prefix_ = "GROUPS";
        res.push_back(copy);
      }
      break;
    }
    case kFrameBoundStart: {
      /*
      frame_bound
      UNBOUNDED PRECEDING
      */
      if (input->left_ != NULL)
        res.push_back(new IR(kFrameBoundStart, OP3("UNBOUNDED PRECEDING", "", "")));
      else {
        auto frame_bound_node = get_ir_from_library(kFrameBound);
        if (frame_bound_node != empty_ir) {
          auto tmp = new IR(input, deep_copy(frame_bound_node), NULL);
          tmp->op_->prefix_ = "";
          tmp->operand_num_ = 1;
          res.push_back(tmp);
        }
      }
      break;
    }
    case kFrameBoundEnd: {
      /*
      frame_bound
      UNBOUNDED FOLLOWING
      */
      if (input->left_ != NULL)
        res.push_back(new IR(kFrameBoundEnd, OP3("UNBOUNDED FOLLOWING", "", "")));
      else {
        auto frame_bound_node = get_ir_from_library(kFrameBound);
        if (frame_bound_node != empty_ir) {
          auto tmp = new IR(input, deep_copy(frame_bound_node), NULL);
          tmp->op_->prefix_ = "";
          tmp->operand_num_ = 1;
          res.push_back(tmp);
        }
      }
      break;
    }
    case kFrameBound: {
      /*
      expr PRECEDING
      expr FOLLOWING
      CURRENT ROW
      */
      if (input->left_ != NULL) {
        res.push_back(new IR(kFrameBound, OP3("CURRENT ROW", "", "")));
        if (input->op_->middle_ != "PRECEDING") {
          auto copy = deep_copy(input);
          copy->op_->middle_ = "PRECEDING";
          res.push_back(copy);
        }
        if (input->op_->middle_ != "FOLLOWING") {
          auto copy = deep_copy(input);
          copy->op_->middle_ = "FOLLOWING";
          res.push_back(copy);
        }
      } else {
        auto expr_node = get_ir_from_library(kExpr);
        if (expr_node != empty_ir) {
          auto tmp = new IR(kFrameBound, OP3("", "PRECEDING", ""), deep_copy(expr_node));
          res.push_back(tmp);
          tmp = new IR(kFrameBound, OP3("", "FOLLOWING", ""), deep_copy(get_ir_from_library(kExpr)));
          res.push_back(tmp);
        }
      }
      break;
    }
    case kOptExistWindowName: {
      /*
      identifier
      (null)
      */
      if (input->left_ != NULL)
        res.push_back(new IR(kOptExistWindowName, string("")));
      else {
        auto identifier_node = get_ir_from_library(kIdentifier);
        if (identifier_node != empty_ir) {
          auto tmp = new IR(kOptExistWindowName, OP3("", "", ""), deep_copy(identifier_node));
          res.push_back(tmp);
        }
      }
      for (auto node : res) {
        if (node->left_ == NULL)
          continue;
        auto identifier_node = node->left_;
        identifier_node->data_type_ = kDataWindowName;
        identifier_node->scope_ = 1;
        identifier_node->data_flag_ = kUse;
      }
      break;
    }
    case kOptGroupClause: {
      /*
      GROUP BY expr_list opt_having_clause
      (null)
      */
      if (input->left_ != NULL)
        res.push_back(new IR(kOptGroupClause, string("")));
      else {
        auto expr_list_node = get_ir_from_library(kExprList);
        auto opt_having_clause_node = get_ir_from_library(kOptHavingClause);
        if (expr_list_node != empty_ir && opt_having_clause_node != empty_ir) {
          auto tmp = new IR(kOptGroupClause, OP3("GROUP BY", "", ""), deep_copy(expr_list_node), deep_copy(opt_having_clause_node));
          res.push_back(tmp);
        }
      }
      break;
    }
    case kOptHavingClause: {
      /*
      HAVING expr
      (null)
      */
      if (input->left_ != NULL)
        res.push_back(new IR(kOptHavingClause, string("")));
      else {
        auto expr_node = get_ir_from_library(kExpr);
        if (expr_node != empty_ir) {
          auto tmp = new IR(kOptHavingClause, OP3("HAVING", "", ""), deep_copy(expr_node));
          res.push_back(tmp);
        }
      }
      break;
    }
    case kOptWhereClause: {
      /*
      where_clause
      (null)
      */
      if (input->left_ != NULL)
        res.push_back(new IR(kOptWhereClause, string("")));
      else {
        auto where_clause_node = get_ir_from_library(kWhereClause);
        if (where_clause_node != empty_ir) {
          auto tmp = new IR(kOptWhereClause, OP3("", "", ""), deep_copy(where_clause_node));
          res.push_back(tmp);
        }
      }
      break;
    }
    case kWhereClause:
      /*
      WHERE expr
      */
      break;
    case kFromClause:
      /*
      FROM table_ref
      */
      break;
    case kTableRef: {
      /*
      opt_table_prefix table_name opt_as_alias opt_index opt_on opt_using
      opt_table_prefix function_name OP_LP expr_list OP_RP opt_as_alias opt_on opt_using
      opt_table_prefix OP_LP select_no_parens OP_RP opt_as_alias opt_on opt_using
      opt_table_prefix OP_LP table_ref OP_RP opt_as_alias opt_on opt_using
      */
      if (input->left_->left_->right_->type_ == kOptIndex) {
        auto opt_table_prefix_node = input->left_->left_->left_->left_->left_;
        auto opt_as_alias_node = input->left_->left_->left_->right_;
        auto opt_on_node = input->left_->right_;
        auto opt_using_node = input->right_;
        auto function_name_node = get_ir_from_library(kFunctionName);
        auto expr_list_node = get_ir_from_library(kExprList);
        if (function_name_node != empty_ir && expr_list_node != empty_ir) {
          auto tmp = new IR(kUnknown, OP3("", "", "("), deep_copy(opt_table_prefix_node), deep_copy(function_name_node));
          tmp = new IR(kUnknown, OP3("", "", ")"), tmp, deep_copy(expr_list_node));
          tmp = new IR(kUnknown, OP3("", "", ""), tmp, deep_copy(opt_as_alias_node));
          tmp = new IR(kUnknown, OP3("", "", ""), tmp, deep_copy(opt_on_node));
          tmp = new IR(input, tmp, deep_copy(opt_using_node));
          res.push_back(tmp);
        }
        auto select_no_parens_node = get_ir_from_library(kSelectNoParens);
        if (select_no_parens_node != empty_ir) {
          auto tmp = new IR(kUnknown, OP3("", "(", ")"), deep_copy(opt_table_prefix_node), deep_copy(select_no_parens_node));
          tmp = new IR(kUnknown, OP3("", "", ""), tmp, deep_copy(opt_as_alias_node));
          tmp = new IR(kUnknown, OP3("", "", ""), tmp, deep_copy(opt_on_node));
          tmp = new IR(input, tmp, deep_copy(opt_using_node));
          res.push_back(tmp);
        }
        auto table_ref_node = get_ir_from_library(kTableRef);
        if (table_ref_node != empty_ir) {
          auto tmp = new IR(kUnknown, OP3("", "(", ")"), deep_copy(opt_table_prefix_node), deep_copy(table_ref_node));
          tmp = new IR(kUnknown, OP3("", "", ""), tmp, deep_copy(opt_as_alias_node));
          tmp = new IR(kUnknown, OP3("", "", ""), tmp, deep_copy(opt_on_node));
          tmp = new IR(input, tmp, deep_copy(opt_using_node));
          res.push_back(tmp);
        }
      }
      if (input->left_->left_->right_->type_ == kOptAsAlias) {
        auto opt_as_alias_node = input->left_->left_->right_;
        auto opt_on_node = input->left_->right_;
        auto opt_using_node = input->right_;
        IR* opt_table_prefix_node;
        if (input->left_->left_->left_->right_->type_ == kExprList) {
          opt_table_prefix_node = input->left_->left_->left_->left_->left_;
        } else {
          opt_table_prefix_node = input->left_->left_->left_->left_;
        }
        auto table_name_node = get_ir_from_library(kTableName);
        auto opt_index_node = get_ir_from_library(kOptIndex);
        if (table_name_node != empty_ir && opt_index_node != empty_ir) {
          auto tmp = new IR(kUnknown, OP3("", "", ""), deep_copy(opt_table_prefix_node), deep_copy(table_name_node));
          tmp = new IR(kUnknown, OP3("", "", ""), tmp, deep_copy(opt_as_alias_node));
          tmp = new IR(kUnknown, OP3("", "", ""), tmp, deep_copy(opt_index_node));
          tmp = new IR(kUnknown, OP3("", "", ""), tmp, deep_copy(opt_on_node));
          tmp = new IR(input, tmp, deep_copy(opt_using_node));
          res.push_back(tmp);
        }
        if (input->left_->left_->left_->right_->type_ == kExprList) {
          auto select_no_parens_node = get_ir_from_library(kSelectNoParens);
          if (select_no_parens_node != empty_ir) {
            auto tmp = new IR(kUnknown, OP3("", "(", ")"), deep_copy(opt_table_prefix_node), deep_copy(select_no_parens_node));
            tmp = new IR(kUnknown, OP3("", "", ""), tmp, deep_copy(opt_as_alias_node));
            tmp = new IR(kUnknown, OP3("", "", ""), tmp, deep_copy(opt_on_node));
            tmp = new IR(input, tmp, deep_copy(opt_using_node));
            res.push_back(tmp);
          }
          auto table_ref_node = get_ir_from_library(kTableRef);
          if (table_ref_node != empty_ir) {
            auto tmp = new IR(kUnknown, OP3("", "(", ")"), deep_copy(opt_table_prefix_node), deep_copy(table_ref_node));
            tmp = new IR(kUnknown, OP3("", "", ""), tmp, deep_copy(opt_as_alias_node));
            tmp = new IR(kUnknown, OP3("", "", ""), tmp, deep_copy(opt_on_node));
            tmp = new IR(input, tmp, deep_copy(opt_using_node));
            res.push_back(tmp);
          }
        } else {
          auto function_name_node = get_ir_from_library(kFunctionName);
          auto expr_list_node = get_ir_from_library(kExprList);
          if (function_name_node != empty_ir && expr_list_node != empty_ir) {
            auto tmp = new IR(kUnknown, OP3("", "", "("), deep_copy(opt_table_prefix_node), deep_copy(function_name_node));
            tmp = new IR(kUnknown, OP3("", "", ")"), tmp, deep_copy(expr_list_node));
            tmp = new IR(kUnknown, OP3("", "", ""), tmp, deep_copy(opt_as_alias_node));
            tmp = new IR(kUnknown, OP3("", "", ""), tmp, deep_copy(opt_on_node));
            tmp = new IR(input, tmp, deep_copy(opt_using_node));
            res.push_back(tmp);
          }
          if (input->left_->left_->left_->right_->type_ != kSelectNoParens) {
            auto select_no_parens_node = get_ir_from_library(kSelectNoParens);
            if (select_no_parens_node != empty_ir) {
              auto copy = deep_copy(input);
              deep_delete(copy->left_->left_->left_->right_);
              copy->left_->left_->left_->right_ = deep_copy(select_no_parens_node);
              res.push_back(copy);
            }
          } else {
            auto table_ref_node = get_ir_from_library(kTableRef);
            if (table_ref_node != empty_ir) {
              auto copy = deep_copy(input);
              deep_delete(copy->left_->left_->left_->right_);
              copy->left_->left_->left_->right_ = deep_copy(table_ref_node);
              res.push_back(copy);
            }
          }
        }
      }
      break;
    }
    case kOptIndex: {
      /*
      INDEXED BY column_name
      NOT INDEXED
      (null)
      */
      if (input->left_ != NULL) {
        res.push_back(new IR(kOptIndex, OP3("NOT INDEXED", "", "")));
        res.push_back(new IR(kOptIndex, string("")));
      } else {
        auto column_name_node = get_ir_from_library(kColumnName);
        if (column_name_node != empty_ir) {
          auto tmp = new IR(kOptIndex, OP3("INDEXED BY", "", ""), deep_copy(column_name_node));
          res.push_back(tmp);
        }
        if (input->op_ != NULL)
          res.push_back(new IR(kOptIndex, string("")));
        else
          res.push_back(new IR(kOptIndex, OP3("NOT INDEXED", "", "")));
      }
      break;
    }
    case kOptOn: {
      /*
      ON expr
      %prec JOIN
      */
      if (input->left_ != NULL)
        res.push_back(new IR(kOptOn, string("")));
      else {
        auto expr_node = get_ir_from_library(kExpr);
        if (expr_node != empty_ir) {
          auto tmp = new IR(kOptOn, OP3("ON", "", ""), deep_copy(expr_node));
          res.push_back(tmp);
        }
      }
      break;
    }
    case kOptUsing: {
      /*
      USING OP_LP column_name_list OP_RP
      (null)
      */
      if (input->left_ != NULL)
        res.push_back(new IR(kOptUsing, string("")));
      else {
        auto column_name_list_node = get_ir_from_library(kColumnNameList);
        if (column_name_list_node != empty_ir) {
          auto tmp = new IR(kOptUsing, OP3("USING (", ")", ""), deep_copy(column_name_list_node));
          res.push_back(tmp);
        }
      }
      break;
    }
    case kColumnNameList: {
      /*
      column_name
      column_name OP_COMMA column_name_list
      */
      if (input->right_ == NULL) {
        auto column_name_list_node = get_ir_from_library(kColumnNameList);
        if (column_name_list_node != empty_ir) {
          auto tmp = new IR(input, deep_copy(input->left_), deep_copy(column_name_list_node));
          tmp->operand_num_ = 2;
          tmp->op_->middle_ = ",";
          res.push_back(tmp);
        }
      } else {
        auto copy = deep_copy(input);
        deep_delete(copy->right_);
        copy->right_ = NULL;
        copy->operand_num_ = 1;
        copy->op_->middle_ = "";
        res.push_back(copy);
      }
      break;
    }
    case kOptTablePrefix: {
      /*
      table_ref join_op
      (null)
      */
      if (input->left_ != NULL)
        res.push_back(new IR(kOptTablePrefix, string("")));
      else {
        auto table_ref_node = get_ir_from_library(kTableRef);
        auto join_op_node = get_ir_from_library(kJoinOp);
        if (table_ref_node != empty_ir && join_op_node != empty_ir) {
          auto tmp = new IR(kOptTablePrefix, OP3("", "", ""), deep_copy(table_ref_node), deep_copy(join_op_node));
          res.push_back(tmp);
        }
      }
      break;
    }
    case kJoinOp: {
      /*
      OP_COMMA
      JOIN
      NATURAL opt_join_type JOIN
      */
      if (input->left_ != NULL) {
        res.push_back(new IR(kJoinOp, OP3(",", "", "")));
        res.push_back(new IR(kJoinOp, OP3("JOIN", "", "")));
      } else {
        if (input->op_->prefix_ != ",")
          res.push_back(new IR(kJoinOp, OP3(",", "", "")));
        else
          res.push_back(new IR(kJoinOp, OP3("JOIN", "", "")));
        auto opt_join_type_node = get_ir_from_library(kOptJoinType);
        if (opt_join_type_node != empty_ir) {
          auto tmp = new IR(kJoinOp, OP3("NATURAL", "JOIN", ""), deep_copy(opt_join_type_node));
          res.push_back(tmp);
        }
      }
      break;
    }
    case kOptJoinType: {
      /*
      LEFT
      LEFT OUTER
      INNER
      CROSS
      (null)
      */
      if (input->op_ == NULL || input->op_->prefix_ != "LEFT") {
        if (input->op_) {
          auto copy = deep_copy(input);
          copy->op_->prefix_ = "LEFT";
          res.push_back(copy);
        } else {
          res.push_back(new IR(kOptJoinType, OP3("LEFT", "", "")));
        }
      }
      if (input->op_ == NULL || input->op_->prefix_ != "LEFT OUTER") {
        if (input->op_) {
          auto copy = deep_copy(input);
          copy->op_->prefix_ = "LEFT OUTER";
          res.push_back(copy);
        } else {
          res.push_back(new IR(kOptJoinType, OP3("LEFT OUTER", "", "")));
        }
      }
      if (input->op_ == NULL || input->op_->prefix_ != "INNER") {
        if (input->op_) {
          auto copy = deep_copy(input);
          copy->op_->prefix_ = "INNER";
          res.push_back(copy);
        } else {
          res.push_back(new IR(kOptJoinType, OP3("INNER", "", "")));
        }
      }
      if (input->op_ == NULL || input->op_->prefix_ != "CROSS") {
        if (input->op_) {
          auto copy = deep_copy(input);
          copy->op_->prefix_ = "CROSS";
          res.push_back(copy);
        } else {
          res.push_back(new IR(kOptJoinType, OP3("CROSS", "", "")));
        }
      }
      if (input->op_ != NULL)
        res.push_back(new IR(kOptJoinType, string("")));
      break;
    }
    case kExprList: {
      /*
      expr opt_as_alias OP_COMMA expr_list
      expr opt_as_alias
      */
      if (input->left_->type_ == kUnknown) {
        auto copy = deep_copy(input->left_);
        copy->type_ = kExprList;
        copy->op_->suffix_ = "";
        res.push_back(copy);
      } else {
        auto expr_list_node = get_ir_from_library(kExprList);
        if (expr_list_node != empty_ir) {
          auto copy = deep_copy(input);
          copy->type_ = kUnknown;
          copy->op_->suffix_ = ",";
          auto tmp = new IR(input, copy, deep_copy(expr_list_node));
          res.push_back(tmp);
        }
      }
      break;
    }
    case kOptLimitClause: {
      /*
      limit_clause
      (null)
      */
      if (input->left_ != NULL)
        res.push_back(new IR(kOptLimitClause, string("")));
      else {
        auto limit_clause_node = get_ir_from_library(kLimitClause);
        if (limit_clause_node != empty_ir) {
          auto tmp = new IR(kOptLimitClause, OP3("", "", ""), deep_copy(limit_clause_node));
          res.push_back(tmp);
        }
      }
      break;
    }
    case kLimitClause: {
      /*
      LIMIT expr
      LIMIT expr OFFSET expr
      LIMIT expr OP_COMMA expr
      */
      if (input->right_ == NULL) {
        auto expr_node = get_ir_from_library(kExpr);
        if (expr_node != empty_ir) {
          auto copy = deep_copy(input);
          copy->right_ = deep_copy(expr_node);
          copy->operand_num_ = 2;
          copy->op_->middle_ = "OFFSET";
          res.push_back(copy);

          copy = deep_copy(input);
          copy->right_ = deep_copy(get_ir_from_library(kExpr));
          copy->operand_num_ = 2;
          copy->op_->middle_ = ",";
          res.push_back(copy);
        }
      } else {
        auto copy = deep_copy(input);
        deep_delete(copy->right_);
        copy->right_ = NULL;
        copy->op_->middle_ = "";
        res.push_back(copy);

        if (input->op_->middle_ == "OFFSET") {
          copy = deep_copy(input);
          copy->op_->middle_ = ",";
          res.push_back(copy);
        } else {
          copy = deep_copy(input);
          copy->op_->middle_ = "OFFSET";
          res.push_back(copy);
        }
      }
      break;
    }
    case kOptLimitRowCount: {
      /*
      LIMIT expr
      (null)
      */
      if (input->left_ != NULL)
        res.push_back(new IR(kOptLimitRowCount, string("")));
      else {
        auto expr_node = get_ir_from_library(kExpr);
        if (expr_node != empty_ir) {
          auto tmp = new IR(kOptLimitRowCount, OP3("LIMIT", "", ""), deep_copy(expr_node));
          res.push_back(tmp);
        }
      }
      break;
    }
    case kOptOrderClause: {
      /*
      ORDER BY order_item_list
      (null)
      */
      if (input->left_ != NULL)
        res.push_back(new IR(kOptOrderClause, string("")));
      else {
        auto order_item_list_node = get_ir_from_library(kOrderItemList);
        if (order_item_list_node != empty_ir) {
          auto tmp = new IR(kOptOrderClause, OP3("ORDER BY", "", ""), deep_copy(order_item_list_node));
          res.push_back(tmp);
        }
      }
      break;
    }
    case kOptOrderNulls: {
      /*
      NULLS FIRST
      NULLS LAST
      (null)
      */
      if (input->op_ == NULL || input->op_->prefix_ != "NULLS FIRST") {
        if (input->op_) {
          auto copy = deep_copy(input);
          copy->op_->prefix_ = "NULLS FIRST";
          res.push_back(copy);
        } else {
          res.push_back(new IR(kOptOrderNulls, OP3("NULLS FIRST", "", "")));
        }
      }
      if (input->op_ == NULL || input->op_->prefix_ != "NULLS LAST") {
        if (input->op_) {
          auto copy = deep_copy(input);
          copy->op_->prefix_ = "NULLS LAST";
          res.push_back(copy);
        } else {
          res.push_back(new IR(kOptOrderNulls, OP3("NULLS LAST", "", "")));
        }
      }
      if (input->op_ != NULL)
        res.push_back(new IR(kOptOrderNulls, string("")));
      break;
    }
    case kOrderItemList: {
      /*
      order_item
      order_item OP_COMMA order_item_list
      */
      if (input->right_ == NULL) {
        auto order_item_list_node = get_ir_from_library(kOrderItemList);
        if (order_item_list_node != empty_ir) {
          auto tmp = new IR(input, deep_copy(input->left_), deep_copy(order_item_list_node));
          tmp->operand_num_ = 2;
          tmp->op_->middle_ = ",";
          res.push_back(tmp);
        }
      } else {
        auto copy = deep_copy(input);
        deep_delete(copy->right_);
        copy->right_ = NULL;
        copy->operand_num_ = 1;
        copy->op_->middle_ = "";
        res.push_back(copy);
      }
      break;
    }
    case kOrderItem:
      /*
      expr opt_order_behavior opt_order_nulls
      */
      break;
    case kOptOrderBehavior: {
      /*
      ASC
      DESC
      (null)
      */
      if (input->op_ == NULL || input->op_->prefix_ != "ASC") {
        if (input->op_) {
          auto copy = deep_copy(input);
          copy->op_->prefix_ = "ASC";
          res.push_back(copy);
        } else {
          res.push_back(new IR(kOptOrderBehavior, OP3("ASC", "", "")));
        }
      }
      if (input->op_ == NULL || input->op_->prefix_ != "DESC") {
        if (input->op_) {
          auto copy = deep_copy(input);
          copy->op_->prefix_ = "DESC";
          res.push_back(copy);
        } else {
          res.push_back(new IR(kOptOrderBehavior, OP3("DESC", "", "")));
        }
      }
      if (input->op_ != NULL)
        res.push_back(new IR(kOptOrderBehavior, string("")));
      break;
    }
    case kOptWithClause: {
      /*
      WITH cte_table_list
      WITH RECURSIVE cte_table_list
      (null)
      */
      if (input->left_ != NULL) {
        res.push_back(new IR(kOptWithClause, string("")));
        if (input->op_->prefix_ != "WITH") {
          auto copy = deep_copy(input);
          copy->op_->prefix_ = "WITH";
          res.push_back(copy);
        } else {
          auto copy = deep_copy(input);
          copy->op_->prefix_ = "WITH RECURSIVE";
          res.push_back(copy);
        }
      } else {
        auto cte_table_list_node = get_ir_from_library(kCteTableList);
        if (cte_table_list_node != empty_ir) {
          auto tmp = new IR(kOptWithClause, OP3("WITH", "", ""), deep_copy(cte_table_list_node));
          res.push_back(tmp);
          tmp = new IR(kOptWithClause, OP3("WITH RECURSIVE", "", ""), deep_copy(get_ir_from_library(kCteTableList)));
          res.push_back(tmp);
        }
      }
      break;
    }
    case kCteTableList: {
      /*
      cte_table
      cte_table OP_COMMA cte_table_list
      */
      if (input->right_ == NULL) {
        auto cte_table_list_node = get_ir_from_library(kCteTableList);
        if (cte_table_list_node != empty_ir) {
          auto tmp = new IR(input, deep_copy(input->left_), deep_copy(cte_table_list_node));
          tmp->operand_num_ = 2;
          tmp->op_->middle_ = ",";
          res.push_back(tmp);
        }
      } else {
        auto copy = deep_copy(input);
        deep_delete(copy->right_);
        copy->right_ = NULL;
        copy->operand_num_ = 1;
        copy->op_->middle_ = "";
        res.push_back(copy);
      }
      break;
    }
    case kCteTable:
      /*
      cte_table_name AS OP_LP select_stmt OP_RP
      */
      break;
    case kCteTableName:
      /*
      table_name opt_column_name_list_p
      */
      break;
    case kOptAllOrDistinct: {
      /*
      ALL
      DISTINCT
      (null)
      */
      if (input->op_ == NULL || input->op_->prefix_ != "ALL") {
        if (input->op_) {
          auto copy = deep_copy(input);
          copy->op_->prefix_ = "ALL";
          res.push_back(copy);
        } else {
          res.push_back(new IR(kOptAllOrDistinct, OP3("ALL", "", "")));
        }
      }
      if (input->op_ == NULL || input->op_->prefix_ != "DISTINCT") {
        if (input->op_) {
          auto copy = deep_copy(input);
          copy->op_->prefix_ = "DISTINCT";
          res.push_back(copy);
        } else {
          res.push_back(new IR(kOptAllOrDistinct, OP3("DISTINCT", "", "")));
        }
      }
      if (input->op_ != NULL)
        res.push_back(new IR(kOptAllOrDistinct, string("")));
      break;
    }
    case kOptTableOptionList: {
      /*
      table_option_list
      (null)
      */
      if (input->left_ != NULL)
        res.push_back(new IR(kOptTableOptionList, string("")));
      else {
        auto table_option_list_node = get_ir_from_library(kTableOptionList);
        if (table_option_list_node != empty_ir) {
          auto tmp = new IR(kOptTableOptionList, OP3("", "", ""), deep_copy(table_option_list_node));
          res.push_back(tmp);
        }
      }
      break;
    }
    case kTableOptionList: {
      /*
      table_option
      table_option opt_op_comma table_option_list
      */
      if (input->right_ == NULL) {
        auto table_option_node = input->left_;
        auto opt_op_comma_node = get_ir_from_library(kOptOpComma);
        auto table_option_list_node = get_ir_from_library(kTableOptionList);
        if (opt_op_comma_node != empty_ir && table_option_list_node != empty_ir) {
          auto tmp = new IR(kUnknown, OP3("", "", ""), deep_copy(table_option_node), deep_copy(opt_op_comma_node));
          tmp = new IR(input, tmp, deep_copy(table_option_list_node));
          tmp->operand_num_ = 2;
          res.push_back(tmp);
        }
      } else {
        auto tmp = new IR(input, deep_copy(input->left_->left_), NULL);
        tmp->operand_num_ = 1;
        res.push_back(tmp);
      }
      break;
    }
    case kTableOption: {
      /*
      INSERT_METHOD opt_op_equal NO
      INSERT_METHOD opt_op_equal FIRST
      INSERT_METHOD opt_op_equal LAST
      ROW_FORMAT opt_op_equal DEFAULT
      ROW_FORMAT opt_op_equal DYNAMIC
      ROW_FORMAT opt_op_equal FIXED
      ROW_FORMAT opt_op_equal COMPRESSED
      ROW_FORMAT opt_op_equal REDUNDANT
      ROW_FORMAT opt_op_equal COMPACT
      */
      if (input->op_->prefix_ != "INSERT_METHOD" || input->op_->middle_ != "NO") {
        auto copy = deep_copy(input);
        copy->op_->prefix_ = "INSERT_METHOD";
        copy->op_->middle_ = "NO";
        res.push_back(copy);
      }
      if (input->op_->prefix_ != "INSERT_METHOD" || input->op_->middle_ != "FIRST") {
        auto copy = deep_copy(input);
        copy->op_->prefix_ = "INSERT_METHOD";
        copy->op_->middle_ = "FIRST";
        res.push_back(copy);
      }
      if (input->op_->prefix_ != "INSERT_METHOD" || input->op_->middle_ != "LAST") {
        auto copy = deep_copy(input);
        copy->op_->prefix_ = "INSERT_METHOD";
        copy->op_->middle_ = "LAST";
        res.push_back(copy);
      }
      if (input->op_->prefix_ != "ROW_FORMAT" || input->op_->middle_ != "DEFAULT") {
        auto copy = deep_copy(input);
        copy->op_->prefix_ = "ROW_FORMAT";
        copy->op_->middle_ = "DEFAULT";
        res.push_back(copy);
      }
      if (input->op_->prefix_ != "ROW_FORMAT" || input->op_->middle_ != "DYNAMIC") {
        auto copy = deep_copy(input);
        copy->op_->prefix_ = "ROW_FORMAT";
        copy->op_->middle_ = "DYNAMIC";
        res.push_back(copy);
      }
      if (input->op_->prefix_ != "ROW_FORMAT" || input->op_->middle_ != "FIXED") {
        auto copy = deep_copy(input);
        copy->op_->prefix_ = "ROW_FORMAT";
        copy->op_->middle_ = "FIXED";
        res.push_back(copy);
      }
      if (input->op_->prefix_ != "ROW_FORMAT" || input->op_->middle_ != "COMPRESSED") {
        auto copy = deep_copy(input);
        copy->op_->prefix_ = "ROW_FORMAT";
        copy->op_->middle_ = "COMPRESSED";
        res.push_back(copy);
      }
      if (input->op_->prefix_ != "ROW_FORMAT" || input->op_->middle_ != "REDUNDANT") {
        auto copy = deep_copy(input);
        copy->op_->prefix_ = "ROW_FORMAT";
        copy->op_->middle_ = "REDUNDANT";
        res.push_back(copy);
      }
      if (input->op_->prefix_ != "ROW_FORMAT" || input->op_->middle_ != "COMPACT") {
        auto copy = deep_copy(input);
        copy->op_->prefix_ = "ROW_FORMAT";
        copy->op_->middle_ = "COMPACT";
        res.push_back(copy);
      }
      break;
    }
    case kOptOpComma: {
      /*
      OP_COMMA
      (null)
      */
      if (input->op_ == NULL) {
        res.push_back(new IR(kOptOpComma, OP3(",", "", "")));
      }
      if (input->op_ != NULL)
        res.push_back(new IR(kOptOpComma, string("")));
      break;
    }
    case kOptIgnoreOrReplace: {
      /*
      IGNORE
      REPLACE
      (null)
      */
      if (input->op_ == NULL || input->op_->prefix_ != "IGNORE") {
        if (input->op_) {
          auto copy = deep_copy(input);
          copy->op_->prefix_ = "IGNORE";
          res.push_back(copy);
        } else {
          res.push_back(new IR(kOptIgnoreOrReplace, OP3("IGNORE", "", "")));
        }
      }
      if (input->op_ == NULL || input->op_->prefix_ != "REPLACE") {
        if (input->op_) {
          auto copy = deep_copy(input);
          copy->op_->prefix_ = "REPLACE";
          res.push_back(copy);
        } else {
          res.push_back(new IR(kOptIgnoreOrReplace, OP3("REPLACE", "", "")));
        }
      }
      if (input->op_ != NULL)
        res.push_back(new IR(kOptIgnoreOrReplace, string("")));
      break;
    }
    case kOptViewAlgorithm: {
      /*
      ALGORITHM OP_EQUAL UNDEFINED
      ALGORITHM OP_EQUAL MERGE
      ALGORITHM OP_EQUAL TEMPTABLE
      (null)
      */
      if (input->op_ == NULL || input->op_->prefix_ != "ALGORITHM = UNDEFINED") {
        if (input->op_) {
          auto copy = deep_copy(input);
          copy->op_->prefix_ = "ALGORITHM = UNDEFINED";
          res.push_back(copy);
        } else {
          res.push_back(new IR(kOptViewAlgorithm, OP3("ALGORITHM = UNDEFINED", "", "")));
        }
      }
      if (input->op_ == NULL || input->op_->prefix_ != "ALGORITHM = MERGE") {
        if (input->op_) {
          auto copy = deep_copy(input);
          copy->op_->prefix_ = "ALGORITHM = MERGE";
          res.push_back(copy);
        } else {
          res.push_back(new IR(kOptViewAlgorithm, OP3("ALGORITHM = MERGE", "", "")));
        }
      }
      if (input->op_ == NULL || input->op_->prefix_ != "ALGORITHM = TEMPTABLE") {
        if (input->op_) {
          auto copy = deep_copy(input);
          copy->op_->prefix_ = "ALGORITHM = TEMPTABLE";
          res.push_back(copy);
        } else {
          res.push_back(new IR(kOptViewAlgorithm, OP3("ALGORITHM = TEMPTABLE", "", "")));
        }
      }
      if (input->op_ != NULL)
        res.push_back(new IR(kOptViewAlgorithm, string("")));
      break;
    }
    case kOptSqlSecurity: {
      /*
      SQL SECURITY DEFINER
      SQL SECURITY INVOKER
      (null)
      */
      if (input->op_ == NULL || input->op_->prefix_ != "SQL SECURITY DEFINER") {
        if (input->op_) {
          auto copy = deep_copy(input);
          copy->op_->prefix_ = "SQL SECURITY DEFINER";
          res.push_back(copy);
        } else {
          res.push_back(new IR(kOptSqlSecurity, OP3("SQL SECURITY DEFINER", "", "")));
        }
      }
      if (input->op_ == NULL || input->op_->prefix_ != "SQL SECURITY INVOKER") {
        if (input->op_) {
          auto copy = deep_copy(input);
          copy->op_->prefix_ = "SQL SECURITY INVOKER";
          res.push_back(copy);
        } else {
          res.push_back(new IR(kOptSqlSecurity, OP3("SQL SECURITY INVOKER", "", "")));
        }
      }
      if (input->op_ != NULL)
        res.push_back(new IR(kOptSqlSecurity, string("")));
      break;
    }
    case kOptIndexOption: {
      /*
      USING BTREE
      USING HASH
      (null)
      */
      if (input->op_ == NULL || input->op_->prefix_ != "USING BTREE") {
        if (input->op_) {
          auto copy = deep_copy(input);
          copy->op_->prefix_ = "USING BTREE";
          res.push_back(copy);
        } else {
          res.push_back(new IR(kOptIndexOption, OP3("USING BTREE", "", "")));
        }
      }
      if (input->op_ == NULL || input->op_->prefix_ != "USING HASH") {
        if (input->op_) {
          auto copy = deep_copy(input);
          copy->op_->prefix_ = "USING HASH";
          res.push_back(copy);
        } else {
          res.push_back(new IR(kOptIndexOption, OP3("USING HASH", "", "")));
        }
      }
      if (input->op_ != NULL)
        res.push_back(new IR(kOptIndexOption, string("")));
      break;
    }
    case kOptExtraOption: {
      /*
      index_algorithm_option
      lock_option
      (null)
      */
      if (input->left_ != NULL) {
        if (input->left_->type_ == kIndexAlgorithmOption) {
          auto lock_option_node = get_ir_from_library(kLockOption);
          if (lock_option_node != empty_ir) {
            auto tmp = new IR(input, deep_copy(lock_option_node), NULL);
            res.push_back(tmp);
          }
        } else {
          auto index_algorithm_option_node = get_ir_from_library(kIndexAlgorithmOption);
          if (index_algorithm_option_node != empty_ir) {
            auto tmp = new IR(input, deep_copy(index_algorithm_option_node), NULL);
            res.push_back(tmp);
          }
        }
      } else {
        auto lock_option_node = get_ir_from_library(kLockOption);
        if (lock_option_node != empty_ir) {
          auto tmp = new IR(kOptExtraOption, OP3("", "", ""), deep_copy(lock_option_node));
          res.push_back(tmp);
        }
        auto index_algorithm_option_node = get_ir_from_library(kIndexAlgorithmOption);
        if (index_algorithm_option_node != empty_ir) {
          auto tmp = new IR(kOptExtraOption, OP3("", "", ""), deep_copy(index_algorithm_option_node));
          res.push_back(tmp);
        }
      }
      break;
    }
    case kIndexAlgorithmOption: {
      /*
      ALGORITHM opt_op_equal DEFAULT
      ALGORITHM opt_op_equal INPLACE
      ALGORITHM opt_op_equal COPY
      */
      if (input->op_->middle_ != "DEFAULT") {
        auto copy = deep_copy(input);
        copy->op_->middle_ = "DEFAULT";
        res.push_back(copy);
      }
      if (input->op_->middle_ != "INPLACE") {
        auto copy = deep_copy(input);
        copy->op_->middle_ = "INPLACE";
        res.push_back(copy);
      }
      if (input->op_->middle_ != "COPY") {
        auto copy = deep_copy(input);
        copy->op_->middle_ = "COPY";
        res.push_back(copy);
      }
      break;
    }
    case kLockOption: {
      /*
      LOCK opt_op_equal DEFAULT
      LOCK opt_op_equal NONE
      LOCK opt_op_equal SHARED
      LOCK opt_op_equal EXCLUSIVE
      */
      if (input->op_->middle_ != "DEFAULT") {
        auto copy = deep_copy(input);
        copy->op_->middle_ = "DEFAULT";
        res.push_back(copy);
      }
      if (input->op_->middle_ != "NONE") {
        auto copy = deep_copy(input);
        copy->op_->middle_ = "NONE";
        res.push_back(copy);
      }
      if (input->op_->middle_ != "SHARED") {
        auto copy = deep_copy(input);
        copy->op_->middle_ = "SHARED";
        res.push_back(copy);
      }
      if (input->op_->middle_ != "EXCLUSIVE") {
        auto copy = deep_copy(input);
        copy->op_->middle_ = "EXCLUSIVE";
        res.push_back(copy);
      }
      break;
    }
    case kOptOpEqual: {
      /*
      OP_EQUAL
      (null)
      */
      if (input->op_ == NULL) {
        res.push_back(new IR(kOptOpEqual, OP3("=", "", "")));
      }
      if (input->op_ != NULL)
        res.push_back(new IR(kOptOpEqual, string("")));
      break;
    }
    case kTriggerActionTime: {
      /*
      BEFORE
      AFTER
      */
      if (input->op_->prefix_ != "BEFORE") {
        auto copy = deep_copy(input);
        copy->op_->prefix_ = "BEFORE";
        res.push_back(copy);
      }
      if (input->op_->prefix_ != "AFTER") {
        auto copy = deep_copy(input);
        copy->op_->prefix_ = "AFTER";
        res.push_back(copy);
      }
      break;
    }
    case kOptRestrictOrCascade: {
      /*
      RESTRICT
      CASCADDE
      (null)
      */
      if (input->op_ == NULL || input->op_->prefix_ != "RESTRICT") {
        if (input->op_) {
          auto copy = deep_copy(input);
          copy->op_->prefix_ = "RESTRICT";
          res.push_back(copy);
        } else {
          res.push_back(new IR(kOptRestrictOrCascade, OP3("RESTRICT", "", "")));
        }
      }
      if (input->op_ == NULL || input->op_->prefix_ != "CASCADDE") {
        if (input->op_) {
          auto copy = deep_copy(input);
          copy->op_->prefix_ = "CASCADDE";
          res.push_back(copy);
        } else {
          res.push_back(new IR(kOptRestrictOrCascade, OP3("CASCADDE", "", "")));
        }
      }
      if (input->op_ != NULL)
        res.push_back(new IR(kOptRestrictOrCascade, string("")));
      break;
    }
    case kInsertRest: {
      /*
      opt_column_name_list_p select_no_parens
      opt_column_name_list_p DEFAULT VALUES
      opt_column_name_list_p VALUES super_values_list
      */
      if (input->right_ != NULL) {
        auto copy = deep_copy(input);
        deep_delete(copy->right_);
        copy->right_ = NULL;
        copy->op_->middle_ = "DEFAULT VALUES";
        copy->operand_num_ = 1;
        res.push_back(copy);

        if (input->right_->type_ == kSelectNoParens) {
          auto super_values_list_node = get_ir_from_library(kSuperValuesList);
          if (super_values_list_node != empty_ir) {
            copy = deep_copy(input);
            deep_delete(copy->right_);
            copy->right_ = deep_copy(super_values_list_node);
            copy->op_->middle_ = "VALUES";
            res.push_back(copy);
          }
        } else {
          auto select_no_parens_node = get_ir_from_library(kSelectNoParens);
          if (select_no_parens_node != empty_ir) {
            copy = deep_copy(input);
            deep_delete(copy->right_);
            copy->right_ = deep_copy(select_no_parens_node);
            copy->op_->middle_ = "";
            res.push_back(copy);
          }
        }
      } else {
        auto select_no_parens_node = get_ir_from_library(kSelectNoParens);
        auto super_values_list_node = get_ir_from_library(kSuperValuesList);
        if (select_no_parens_node != empty_ir) {
          auto copy = deep_copy(input);
          copy->right_ = deep_copy(select_no_parens_node);
          copy->op_->middle_ = "";
          copy->operand_num_ = 2;
        }
        if (super_values_list_node != empty_ir) {
          auto copy = deep_copy(input);
          copy->right_ = deep_copy(super_values_list_node);
          copy->op_->middle_ = "VALUES";
          copy->operand_num_ = 2;
        }
      }
      break;
    }
    case kSuperValuesList: {
      /*
      values_list
      values_list OP_COMMA super_values_list
      */
      if (input->right_ == NULL) {
        auto super_values_list_node = get_ir_from_library(kSuperValuesList);
        if (super_values_list_node != empty_ir) {
          auto tmp = new IR(input, deep_copy(input->left_), deep_copy(super_values_list_node));
          tmp->operand_num_ = 2;
          tmp->op_->middle_ = ",";
          res.push_back(tmp);
        }
      } else {
        auto copy = deep_copy(input);
        deep_delete(copy->right_);
        copy->right_ = NULL;
        copy->operand_num_ = 1;
        copy->op_->middle_ = "";
        res.push_back(copy);
      }
      break;
    }
    case kValuesList:
      /*
      OP_LP expr_list OP_RP
      */
      break;
    case kOptOnConflict: {
      /*
      ON CONFLICT opt_conflict_expr DO NOTHING
      ON CONFLICT opt_conflict_expr DO UPDATE set_clause_list where_clause
      (null)
      */
      if (input->left_ != NULL) {
        res.push_back(new IR(kOptOnConflict, string("")));

        if (input->right_ == NULL) {
          auto set_clause_list_node = get_ir_from_library(kSetClauseList);
          auto where_clause_node = get_ir_from_library(kWhereClause);
          if (set_clause_list_node != empty_ir && where_clause_node != empty_ir) {
            auto tmp = deep_copy(input);
            tmp->right_ = deep_copy(set_clause_list_node);
            tmp->type_ = kUnknown;
            tmp->op_->middle_ = "DO UPDATE";
            tmp->operand_num_ = 2;
            tmp = new IR(kOptOnConflict, OP3("", "", ""), tmp, deep_copy(where_clause_node));
            res.push_back(tmp);
          }
        } else {
          auto copy = deep_copy(input->left_);
          deep_delete(copy->right_);
          copy->right_ = NULL;
          copy->type_ = kOptOnConflict;
          copy->op_->middle_ = "DO NOTHING";
          copy->operand_num_ = 1;
          res.push_back(copy);
        }
      } else {
        auto opt_conflict_expr_node = get_ir_from_library(kOptConflictExpr);
        auto set_clause_list_node = get_ir_from_library(kSetClauseList);
        auto where_clause_node = get_ir_from_library(kWhereClause);
        if (opt_conflict_expr_node != empty_ir) {
          auto tmp = new IR(kOptOnConflict, OP3("ON CONFLICT", "DO NOTHING", ""), deep_copy(opt_conflict_expr_node));
          res.push_back(tmp);
          if (set_clause_list_node != empty_ir && where_clause_node != empty_ir) {
            tmp = new IR(kUnknown, OP3("ON CONFLICT", "DO UPDATE", ""), deep_copy(get_ir_from_library(kOptConflictExpr)), deep_copy(set_clause_list_node));
            tmp = new IR(kOptOnConflict, OP3("", "", ""), tmp, deep_copy(where_clause_node));
            res.push_back(tmp);
          }
        }
      }
      break;
    }
    case kOptConflictExpr: {
      /*
      OP_LP indexed_column_list OP_RP where_clause
      (null)
      */
      if (input->left_ != NULL)
        res.push_back(new IR(kOptConflictExpr, string("")));
      else {
        auto indexed_column_list_node = get_ir_from_library(kIndexedColumnList);
        auto where_clause_node = get_ir_from_library(kWhereClause);
        if (indexed_column_list_node != empty_ir && where_clause_node != empty_ir) {
          auto tmp = new IR(kOptConflictExpr, OP3("(", ")", ""), deep_copy(indexed_column_list_node), deep_copy(where_clause_node));
          res.push_back(tmp);
        }
      }
      break;
    }
    case kIndexedColumnList: {
      /*
      indexed_column
      indexed_column OP_COMMA indexed_column_list
      */
      if (input->right_ == NULL) {
        auto indexed_column_list_node = get_ir_from_library(kIndexedColumnList);
        if (indexed_column_list_node != empty_ir) {
          auto tmp = new IR(input, deep_copy(input->left_), deep_copy(indexed_column_list_node));
          tmp->operand_num_ = 2;
          tmp->op_->middle_ = ",";
          res.push_back(tmp);
        }
      } else {
        auto copy = deep_copy(input);
        deep_delete(copy->right_);
        copy->right_ = NULL;
        copy->operand_num_ = 1;
        copy->op_->middle_ = "";
        res.push_back(copy);
      }
      break;
    }
    case kIndexedColumn:
      /*
      expr opt_order_behavior
      */
      break;
    case kAlterAction: {
      /*
      RENAME TO table_name
      RENAME opt_column column_name TO column_name
      ADD opt_column column_def
      DROP opt_column column_name
      alter_constant_action
      */
      if (input->left_->type_ != kTableName) {
        auto table_name_node = get_ir_from_library(kTableName);
        if (table_name_node != empty_ir) {
          auto tmp = new IR(input, deep_copy(table_name_node), NULL);
          tmp->op_->prefix_ = "RENAME TO";
          tmp->operand_num_ = 1;
          res.push_back(tmp);
        }
      }
      if (input->left_->type_ != kUnknown) {
        IR* opt_column_node, *column_name_1_node, *column_name_2_node;
        if (input->left_->type_ == kOptColumn) {
          opt_column_node = input->left_;
        } else {
          opt_column_node = get_ir_from_library(kOptColumn);
        }
        if (input->right_ != NULL && input->right_->type_ == kColumnName) {
          column_name_1_node = input->right_;
        } else {
          column_name_1_node = get_ir_from_library(kColumnName);
        }
        column_name_2_node = get_ir_from_library(kColumnName);
        if (opt_column_node != empty_ir && column_name_2_node != empty_ir) {
          auto tmp = new IR(kUnknown, OP3("RENAME", "", "TO"), deep_copy(opt_column_node), deep_copy(column_name_1_node));
          tmp = new IR(input, tmp, deep_copy(column_name_2_node));
          tmp->op_->prefix_ = "";
          tmp->operand_num_ = 2;
          res.push_back(tmp);
        }
      }
      if (input->op_->prefix_ != "ADD") {
        IR* opt_column_node, *column_def_node;
        if (input->left_->type_ == kOptColumn) {
          opt_column_node = input->left_;
        } else if (input->left_->type_ == kUnknown) {
          opt_column_node = input->left_->left_;
        } else {
          opt_column_node = get_ir_from_library(kOptColumn);
        }
        column_def_node = get_ir_from_library(kColumnDef);
        if (opt_column_node != empty_ir && column_def_node != empty_ir) {
          auto tmp = new IR(input, deep_copy(opt_column_node), deep_copy(column_def_node));
          tmp->op_->prefix_ = "ADD";
          tmp->operand_num_ = 2;
          res.push_back(tmp);
        }
      }
      if (input->op_->prefix_ != "DROP") {
        IR* opt_column_node, *column_name_node;
        if (input->left_->type_ == kOptColumn) {
          opt_column_node = input->left_;
          column_name_node = get_ir_from_library(kColumnName);
        } else if (input->left_->type_ == kUnknown) {
          opt_column_node = input->left_->left_;
          column_name_node = input->left_->right_;
        } else {
          opt_column_node = get_ir_from_library(kOptColumn);
          column_name_node = get_ir_from_library(kColumnName);
        }
        if (opt_column_node != empty_ir && column_name_node != empty_ir) {
          auto tmp = new IR(input, deep_copy(opt_column_node), deep_copy(column_name_node));
          tmp->op_->prefix_ = "DROP";
          tmp->operand_num_ = 2;
          res.push_back(tmp);
        }
      }
      if (input->left_->type_ != kAlterConstantAction) {
        auto alter_constant_action_node = get_ir_from_library(kAlterConstantAction);
        if (alter_constant_action_node != empty_ir) {
          auto tmp = new IR(input, deep_copy(alter_constant_action_node), NULL);
          tmp->op_->prefix_ = "";
          tmp->operand_num_ = 1;
          res.push_back(tmp);
        }
      }
      for (auto node : res) {
        if (node->left_->type_ != kTableName)
          continue;
        auto identifier_node = node->left_->left_;
        identifier_node->data_type_ = kDataTableName;
        identifier_node->scope_ = 2;
        identifier_node->data_flag_ = kReplace;
      }
      for (auto node : res) {
        if (node->left_->type_ != kUnknown)
          continue;
        auto identifier_1_node = node->left_->right_->left_;
        auto identifier_2_node = node->right_->left_;
        identifier_1_node->data_type_ = kDataColumnName;
        identifier_1_node->scope_ = 2;
        identifier_1_node->data_flag_ = kUse;
        identifier_2_node->data_type_ = kDataColumnName;
        identifier_2_node->scope_ = 3;
        identifier_2_node->data_flag_ = kReplace;
      }
      for (auto node : res) {
        if (node->right_->type_ != kColumnDef)
          continue;
        auto identifier_node = node->right_->left_->left_;
        identifier_node->data_type_ = kDataColumnName;
        identifier_node->scope_ = 2;
        identifier_node->data_flag_ = kDefine;
      }
      for (auto node : res) {
        if (node->op_->prefix_ != "DROP")
          continue;
        auto identifier_node = node->right_->left_;
        identifier_node->data_type_ = kDataColumnName;
        identifier_node->scope_ = 2;
        identifier_node->data_flag_ = kUndefine;
      }
      break;
    }
    case kAlterConstantAction: {
      /*
      DROP PRIMARY KEY
      FORCE
      DISABLE KEYS
      ENABLE KEYS
      lock_option
      WITH VALIDATION
      WITHOUT VALIDATION
      */
      if (input->left_ != NULL) {
        res.push_back(new IR(kAlterConstantAction, OP3("DROP PRIMARY KEY", "", "")));
        res.push_back(new IR(kAlterConstantAction, OP3("FORCE", "", "")));
        res.push_back(new IR(kAlterConstantAction, OP3("DISABLE KEYS", "", "")));
        res.push_back(new IR(kAlterConstantAction, OP3("ENABLE KEYS", "", "")));
        res.push_back(new IR(kAlterConstantAction, OP3("WITH VALIDATION", "", "")));
        res.push_back(new IR(kAlterConstantAction, OP3("WITHOUT VALIDATION", "", "")));
      } else {
        auto lock_option_node = get_ir_from_library(kLockOption);
        if (lock_option_node != empty_ir) {
          auto tmp = new IR(kAlterConstantAction, OP3("", "", ""), deep_copy(lock_option_node));
          res.push_back(tmp);
        }

        if (input->op_->prefix_ != "DROP PRIMARY KEY") {
          auto copy = deep_copy(input);
          copy->op_->prefix_ = "DROP PRIMARY KEY";
          res.push_back(copy);
        }
        if (input->op_->prefix_ != "FORCE") {
          auto copy = deep_copy(input);
          copy->op_->prefix_ = "FORCE";
          res.push_back(copy);
        }
        if (input->op_->prefix_ != "DISABLE KEYS") {
          auto copy = deep_copy(input);
          copy->op_->prefix_ = "DISABLE KEYS";
          res.push_back(copy);
        }
        if (input->op_->prefix_ != "ENABLE KEYS") {
          auto copy = deep_copy(input);
          copy->op_->prefix_ = "ENABLE KEYS";
          res.push_back(copy);
        }
        if (input->op_->prefix_ != "WITH VALIDATION") {
          auto copy = deep_copy(input);
          copy->op_->prefix_ = "WITH VALIDATION";
          res.push_back(copy);
        }
        if (input->op_->prefix_ != "WITHOUT VALIDATION") {
          auto copy = deep_copy(input);
          copy->op_->prefix_ = "WITHOUT VALIDATION";
          res.push_back(copy);
        }
      }
      break;
    }
    case kColumnDefList: {
      /*
      column_def
      column_def OP_COMMA column_def_list
      */
      if (input->right_ == NULL) {
        auto column_def_list_node = get_ir_from_library(kColumnDefList);
        if (column_def_list_node != empty_ir) {
          auto tmp = new IR(input, deep_copy(input->left_), deep_copy(column_def_list_node));
          tmp->operand_num_ = 2;
          tmp->op_->middle_ = ",";
          res.push_back(tmp);
        }
      } else {
        auto copy = deep_copy(input);
        deep_delete(copy->right_);
        copy->right_ = NULL;
        copy->operand_num_ = 1;
        copy->op_->middle_ = "";
        res.push_back(copy);
      }
      break;
    }
    case kColumnDef: {
      /*
      identifier type_name opt_column_constraint_list
      */
      for (auto node : res) {
        auto identifier_node = node->left_->left_;
        identifier_node->data_type_ = kDataColumnName;
        identifier_node->scope_ = 2;
        identifier_node->data_flag_ = kDefine;
      }
      break;
    }
    case kOptColumnConstraintList: {
      /*
      column_constraint_list opt_check opt_reference_clause
      (null)
      */
      if (input->left_ != NULL)
        res.push_back(new IR(kOptColumnConstraintList, string("")));
      else {
        auto column_constraint_list_node = get_ir_from_library(kColumnConstraintList);
        auto opt_check_node = get_ir_from_library(kOptCheck);
        auto opt_reference_clause_node = get_ir_from_library(kOptReferenceClause);
        if (column_constraint_list_node != empty_ir && opt_check_node != empty_ir && opt_reference_clause_node != empty_ir) {
          auto tmp = new IR(kUnknown, OP3("", "", ""), deep_copy(column_constraint_list_node), deep_copy(opt_check_node));
          tmp = new IR(kOptColumnConstraintList, OP3("", "", ""), tmp, deep_copy(opt_reference_clause_node));
          res.push_back(tmp);
        }
      }
      break;
    }
    case kColumnConstraintList: {
      /*
      column_constraint
      column_constraint column_constraint_list
      */
      if (input->right_ == NULL) {
        auto column_constraint_list_node = get_ir_from_library(kColumnConstraintList);
        if (column_constraint_list_node != empty_ir) {
          auto tmp = new IR(input, deep_copy(input->left_), deep_copy(column_constraint_list_node));
          tmp->operand_num_ = 2;
          res.push_back(tmp);
        }
      } else {
        auto copy = deep_copy(input);
        deep_delete(copy->right_);
        copy->right_ = NULL;
        copy->operand_num_ = 1;
        res.push_back(copy);
      }
      break;
    }
    case kColumnConstraint:
      /*
      constraint_type
      */
      break;
    case kOptReferenceClause: {
      /*
      opt_foreign_key reference_clause
      (null)
      */
      if (input->left_ != NULL)
        res.push_back(new IR(kOptReferenceClause, string("")));
      else {
        auto opt_foreign_key_node = get_ir_from_library(kOptForeignKey);
        auto reference_clause_node = get_ir_from_library(kReferenceClause);
        if (opt_foreign_key_node != empty_ir && reference_clause_node != empty_ir) {
          auto tmp = new IR(kOptReferenceClause, OP3("", "", ""), deep_copy(opt_foreign_key_node), deep_copy(reference_clause_node));
          res.push_back(tmp);
        }
      }
      break;
    }
    case kOptCheck: {
      /*
      CHECK OP_LP expr OP_RP opt_enforced
      (null)
      */
      if (input->left_ != NULL)
        res.push_back(new IR(kOptCheck, string("")));
      else {
        auto expr_node = get_ir_from_library(kExpr);
        auto opt_enforced_node = get_ir_from_library(kOptEnforced);
        if (expr_node != empty_ir && opt_enforced_node != empty_ir) {
          auto tmp = new IR(kOptCheck, OP3("CHECK (", ")", ""), deep_copy(expr_node), deep_copy(opt_enforced_node));
          res.push_back(tmp);
        }
      }
      break;
    }
    case kConstraintType: {
      /*
      PRIMARY KEY
      NOT NULL
      UNIQUE
      */
      if (input->op_->prefix_ != "PRIMARY KEY") {
        auto copy = deep_copy(input);
        copy->op_->prefix_ = "PRIMARY KEY";
        res.push_back(copy);
      }
      if (input->op_->prefix_ != "NOT NULL") {
        auto copy = deep_copy(input);
        copy->op_->prefix_ = "NOT NULL";
        res.push_back(copy);
      }
      if (input->op_->prefix_ != "UNIQUE") {
        auto copy = deep_copy(input);
        copy->op_->prefix_ = "UNIQUE";
        res.push_back(copy);
      }
      break;
    }
    case kReferenceClause: {
      /*
      REFERENCES table_name opt_column_name_list_p opt_foreign_key_actions opt_constraint_attribute_spec
      */
      for (auto node : res) {
        auto identifier_node = node->left_->left_->left_->left_;
        identifier_node->data_type_ = kDataTableName;
        identifier_node->scope_ = 100;
        identifier_node->data_flag_ = kUse;
      }
      for (auto node : res) {
        auto opt_column_name_list_node = node->left_->left_->right_;
        if (opt_column_name_list_node->left_ != NULL) {
          auto column_name_list_node = opt_column_name_list_node->left_;
          while (column_name_list_node) {
            auto identifier_node = column_name_list_node->left_->left_;
            identifier_node->data_type_ = kDataColumnName;
            identifier_node->scope_ = 101;
            identifier_node->data_flag_ = kUse;
            column_name_list_node = column_name_list_node->right_;
          }
        }
      }
      break;
    }
    case kOptForeignKey: {
      /*
      FOREIGN KEY
      (null)
      */
      if (input->op_ == NULL) {
        res.push_back(new IR(kOptForeignKey, OP3("FOREIGN KEY", "", "")));
      }
      if (input->op_ != NULL)
        res.push_back(new IR(kOptForeignKey, string("")));
      break;
    }
    case kOptForeignKeyActions: {
      /*
      foreign_key_actions
      (null)
      */
      if (input->left_ != NULL)
        res.push_back(new IR(kOptForeignKeyActions, string("")));
      else {
        auto foreign_key_actions_node = get_ir_from_library(kForeignKeyActions);
        if (foreign_key_actions_node != empty_ir) {
          auto tmp = new IR(kOptForeignKeyActions, OP3("", "", ""), deep_copy(foreign_key_actions_node));
          res.push_back(tmp);
        }
      }
      break;
    }
    case kForeignKeyActions: {
      /*
      MATCH FULL
      MATCH PARTIAL
      MATCH SIMPLE
      ON UPDATE key_actions
      ON DELETE key_actions
      */
      if (input->left_ != NULL) {
        res.push_back(new IR(kForeignKeyActions, OP3("MATCH FULL", "", "")));
        res.push_back(new IR(kForeignKeyActions, OP3("MATCH PARTIAL", "", "")));
        res.push_back(new IR(kForeignKeyActions, OP3("MATCH SIMPLE", "", "")));

        if (input->op_->prefix_ == "ON UPDATE") {
          auto copy = deep_copy(input);
          copy->op_->prefix_ = "ON DELETE";
          res.push_back(copy);
        } else {
          auto copy = deep_copy(input);
          copy->op_->prefix_ = "ON UPDATE";
          res.push_back(copy);
        }
      } else {
        auto key_actions_node = get_ir_from_library(kKeyActions);
        if (key_actions_node != empty_ir) {
          res.push_back(new IR(kForeignKeyActions, OP3("ON UPDATE", "", ""), deep_copy(key_actions_node)));
          res.push_back(new IR(kForeignKeyActions, OP3("ON DELETE", "", ""), deep_copy(get_ir_from_library(kKeyActions))));
        }

        if (input->op_->prefix_ != "MATCH FULL") {
          auto copy = deep_copy(input);
          copy->op_->prefix_ = "MATCH FULL";
          res.push_back(copy);
        }
        if (input->op_->prefix_ != "MATCH PARTIAL") {
          auto copy = deep_copy(input);
          copy->op_->prefix_ = "MATCH PARTIAL";
          res.push_back(copy);
        }
        if (input->op_->prefix_ != "MATCH SIMPLE") {
          auto copy = deep_copy(input);
          copy->op_->prefix_ = "MATCH SIMPLE";
          res.push_back(copy);
        }
      }
      break;
    }
    case kKeyActions: {
      /*
      SET NULL
      SET DEFAULT
      CASCADE
      RESTRICT
      NO ACTION
      */
      if (input->op_->prefix_ != "SET NULL") {
        auto copy = deep_copy(input);
        copy->op_->prefix_ = "SET NULL";
        res.push_back(copy);
      }
      if (input->op_->prefix_ != "SET DEFAULT") {
        auto copy = deep_copy(input);
        copy->op_->prefix_ = "SET DEFAULT";
        res.push_back(copy);
      }
      if (input->op_->prefix_ != "CASCADE") {
        auto copy = deep_copy(input);
        copy->op_->prefix_ = "CASCADE";
        res.push_back(copy);
      }
      if (input->op_->prefix_ != "RESTRICT") {
        auto copy = deep_copy(input);
        copy->op_->prefix_ = "RESTRICT";
        res.push_back(copy);
      }
      if (input->op_->prefix_ != "NO ACTION") {
        auto copy = deep_copy(input);
        copy->op_->prefix_ = "NO ACTION";
        res.push_back(copy);
      }
      break;
    }
    case kOptConstraintAttributeSpec: {
      /*
      DEFFERRABLE opt_initial_time
      NOT DEFFERRABLE opt_initial_time
      (null)
      */
      if (input->left_ != NULL) {
        res.push_back(new IR(kOptConstraintAttributeSpec, string("")));

        if (input->op_->prefix_ != "DEFFERRABLE") {
          auto copy = deep_copy(input);
          copy->op_->prefix_ = "DEFFERRABLE";
          res.push_back(copy);
        } else {
          auto copy = deep_copy(input);
          copy->op_->prefix_ = "NOT DEFFERRABLE";
          res.push_back(copy);
        }
      } else {
        auto opt_initial_time_node = get_ir_from_library(kOptInitialTime);
        if (opt_initial_time_node != empty_ir) {
          res.push_back(new IR(kOptConstraintAttributeSpec, OP3("DEFFERRABLE", "", ""), deep_copy(opt_initial_time_node)));
          res.push_back(new IR(kOptConstraintAttributeSpec, OP3("NOT DEFFERRABLE", "", ""), deep_copy(get_ir_from_library(kOptInitialTime))));
        }
      }
      break;
    }
    case kOptInitialTime: {
      /*
      INITIALLY DEFERRED
      INITIALLY IMMEDIATE
      (null)
      */
      if (input->op_ == NULL || input->op_->prefix_ != "INITIALLY DEFERRED") {
        if (input->op_) {
          auto copy = deep_copy(input);
          copy->op_->prefix_ = "INITIALLY DEFERRED";
          res.push_back(copy);
        } else {
          res.push_back(new IR(kOptInitialTime, OP3("INITIALLY DEFERRED", "", "")));
        }
      }
      if (input->op_ == NULL || input->op_->prefix_ != "INITIALLY IMMEDIATE") {
        if (input->op_) {
          auto copy = deep_copy(input);
          copy->op_->prefix_ = "INITIALLY IMMEDIATE";
          res.push_back(copy);
        } else {
          res.push_back(new IR(kOptInitialTime, OP3("INITIALLY IMMEDIATE", "", "")));
        }
      }
      if (input->op_ != NULL)
        res.push_back(new IR(kOptInitialTime, string("")));
      break;
    }
    case kOptTemp: {
      /*
      TEMPORARY
      (null)
      */
      if (input->op_ == NULL) {
        res.push_back(new IR(kOptTemp, OP3("TEMPORARY", "", "")));
      }
      if (input->op_ != NULL)
        res.push_back(new IR(kOptTemp, string("")));
      break;
    }
    case kOptCheckOption: {
      /*
      WITH CHECK OPTION
      WITH CASCADED CHECK OPTION
      WITH LOCAL CHECK OPTION
      (null)
      */
      if (input->op_ == NULL || input->op_->prefix_ != "WITH CHECK OPTION") {
        if (input->op_) {
          auto copy = deep_copy(input);
          copy->op_->prefix_ = "WITH CHECK OPTION";
          res.push_back(copy);
        } else {
          res.push_back(new IR(kOptCheckOption, OP3("WITH CHECK OPTION", "", "")));
        }
      }
      if (input->op_ == NULL || input->op_->prefix_ != "WITH CASCADED CHECK OPTION") {
        if (input->op_) {
          auto copy = deep_copy(input);
          copy->op_->prefix_ = "WITH CASCADED CHECK OPTION";
          res.push_back(copy);
        } else {
          res.push_back(new IR(kOptCheckOption, OP3("WITH CASCADED CHECK OPTION", "", "")));
        }
      }
      if (input->op_ == NULL || input->op_->prefix_ != "WITH LOCAL CHECK OPTION") {
        if (input->op_) {
          auto copy = deep_copy(input);
          copy->op_->prefix_ = "WITH LOCAL CHECK OPTION";
          res.push_back(copy);
        } else {
          res.push_back(new IR(kOptCheckOption, OP3("WITH LOCAL CHECK OPTION", "", "")));
        }
      }
      if (input->op_ != NULL)
        res.push_back(new IR(kOptCheckOption, string("")));
      break;
    }
    case kOptColumnNameListP: {
      /*
      OP_LP column_name_list OP_RP
      (null)
      */
      if (input->left_ != NULL)
        res.push_back(new IR(kOptColumnNameListP, string("")));
      else {
        auto column_name_list_node = get_ir_from_library(kColumnNameList);
        if (column_name_list_node != empty_ir) {
          auto tmp = new IR(kOptColumnNameListP, OP3("(", ")", ""), deep_copy(column_name_list_node));
          res.push_back(tmp);
        }
      }
      break;
    }
    case kSetClauseList: {
      /*
      set_clause
      set_clause OP_COMMA set_clause_list
      */
      if (input->right_ == NULL) {
        auto set_clause_list_node = get_ir_from_library(kSetClauseList);
        if (set_clause_list_node != empty_ir) {
          auto tmp = new IR(input, deep_copy(input->left_), deep_copy(set_clause_list_node));
          tmp->operand_num_ = 2;
          tmp->op_->middle_ = ",";
          res.push_back(tmp);
        }
      } else {
        auto copy = deep_copy(input);
        deep_delete(copy->right_);
        copy->right_ = NULL;
        copy->operand_num_ = 1;
        copy->op_->middle_ = "";
        res.push_back(copy);
      }
      break;
    }
    case kSetClause: {
      /*
      column_name OP_EQUAL expr
      OP_LP column_name_list OP_RP OP_EQUAL expr
      */
      if (input->left_->type_ == kColumnName) {
        auto column_name_list_node = get_ir_from_library(kColumnNameList);
        if (column_name_list_node != empty_ir) {
          auto copy = deep_copy(input);
          deep_delete(copy->left_);
          copy->left_ = deep_copy(column_name_list_node);
          copy->op_->prefix_ = "(";
          copy->op_->middle_ = ") =";
          res.push_back(copy);
        }
      } else {
        auto column_name_node = get_ir_from_library(kColumnName);
        if (column_name_node != empty_ir) {
          auto copy = deep_copy(input);
          deep_delete(copy->left_);
          copy->left_ = deep_copy(column_name_node);
          copy->op_->prefix_ = "";
          copy->op_->middle_ = "=";
          res.push_back(copy);
        }
      }
      break;
    }
    case kOptAsAlias: {
      /*
      as_alias
      (null)
      */
      if (input->left_ != NULL)
        res.push_back(new IR(kOptAsAlias, string("")));
      else {
        auto as_alias_node = get_ir_from_library(kAsAlias);
        if (as_alias_node != empty_ir) {
          auto tmp = new IR(kOptAsAlias, OP3("", "", ""), deep_copy(as_alias_node));
          res.push_back(tmp);
        }
      }
      break;
    }
    case kExpr: {
      /*
      operand
      between_expr
      exists_expr
      in_expr
      cast_expr
      logic_expr
      */
      if (input->left_->type_ != kOperand) {
        auto node = get_ir_from_library(kOperand);
        if (node != empty_ir) {
          auto copy = deep_copy(input);
          deep_delete(copy->left_);
          copy->left_ = deep_copy(node);
          res.push_back(copy);
        }
      }
      if (input->left_->type_ != kBetweenExpr) {
        auto node = get_ir_from_library(kBetweenExpr);
        if (node != empty_ir) {
          auto copy = deep_copy(input);
          deep_delete(copy->left_);
          copy->left_ = deep_copy(node);
          res.push_back(copy);
        }
      }
      if (input->left_->type_ != kExistsExpr) {
        auto node = get_ir_from_library(kExistsExpr);
        if (node != empty_ir) {
          auto copy = deep_copy(input);
          deep_delete(copy->left_);
          copy->left_ = deep_copy(node);
          res.push_back(copy);
        }
      }
      if (input->left_->type_ != kInExpr) {
        auto node = get_ir_from_library(kInExpr);
        if (node != empty_ir) {
          auto copy = deep_copy(input);
          deep_delete(copy->left_);
          copy->left_ = deep_copy(node);
          res.push_back(copy);
        }
      }
      if (input->left_->type_ != kCastExpr) {
        auto node = get_ir_from_library(kCastExpr);
        if (node != empty_ir) {
          auto copy = deep_copy(input);
          deep_delete(copy->left_);
          copy->left_ = deep_copy(node);
          res.push_back(copy);
        }
      }
      if (input->left_->type_ != kLogicExpr) {
        auto node = get_ir_from_library(kLogicExpr);
        if (node != empty_ir) {
          auto copy = deep_copy(input);
          deep_delete(copy->left_);
          copy->left_ = deep_copy(node);
          res.push_back(copy);
        }
      }
      break;
    }
    case kOperand: {
      /*
      OP_LP expr_list OP_RP
      array_index
      scalar_expr
      unary_expr
      binary_expr
      case_expr
      extract_expr
      array_expr
      function_expr
      OP_LP select_no_parens OP_RP
      */
      if (input->left_->type_ != kExprList) {
        auto node = get_ir_from_library(kExprList);
        if (node != empty_ir) {
          auto copy = deep_copy(input);
          deep_delete(copy->left_);
          copy->left_ = deep_copy(node);
          copy->op_->prefix_ = "(";
          copy->op_->middle_ = ")";
          res.push_back(copy);
        }
      }
      if (input->left_->type_ != kArrayIndex) {
        auto node = get_ir_from_library(kArrayIndex);
        if (node != empty_ir) {
          auto copy = deep_copy(input);
          deep_delete(copy->left_);
          copy->left_ = deep_copy(node);
          copy->op_->prefix_ = "";
          copy->op_->middle_ = "";
          res.push_back(copy);
        }
      }
      if (input->left_->type_ != kScalarExpr) {
        auto node = get_ir_from_library(kScalarExpr);
        if (node != empty_ir) {
          auto copy = deep_copy(input);
          deep_delete(copy->left_);
          copy->left_ = deep_copy(node);
          copy->op_->prefix_ = "";
          copy->op_->middle_ = "";
          res.push_back(copy);
        }
      }
      if (input->left_->type_ != kUnaryExpr) {
        auto node = get_ir_from_library(kUnaryExpr);
        if (node != empty_ir) {
          auto copy = deep_copy(input);
          deep_delete(copy->left_);
          copy->left_ = deep_copy(node);
          copy->op_->prefix_ = "";
          copy->op_->middle_ = "";
          res.push_back(copy);
        }
      }
      if (input->left_->type_ != kBinaryExpr) {
        auto node = get_ir_from_library(kBinaryExpr);
        if (node != empty_ir) {
          auto copy = deep_copy(input);
          deep_delete(copy->left_);
          copy->left_ = deep_copy(node);
          copy->op_->prefix_ = "";
          copy->op_->middle_ = "";
          res.push_back(copy);
        }
      }
      if (input->left_->type_ != kCaseExpr) {
        auto node = get_ir_from_library(kCaseExpr);
        if (node != empty_ir) {
          auto copy = deep_copy(input);
          deep_delete(copy->left_);
          copy->left_ = deep_copy(node);
          copy->op_->prefix_ = "";
          copy->op_->middle_ = "";
          res.push_back(copy);
        }
      }
      if (input->left_->type_ != kExtractExpr) {
        auto node = get_ir_from_library(kExtractExpr);
        if (node != empty_ir) {
          auto copy = deep_copy(input);
          deep_delete(copy->left_);
          copy->left_ = deep_copy(node);
          copy->op_->prefix_ = "";
          copy->op_->middle_ = "";
          res.push_back(copy);
        }
      }
      if (input->left_->type_ != kArrayExpr) {
        auto node = get_ir_from_library(kArrayExpr);
        if (node != empty_ir) {
          auto copy = deep_copy(input);
          deep_delete(copy->left_);
          copy->left_ = deep_copy(node);
          copy->op_->prefix_ = "";
          copy->op_->middle_ = "";
          res.push_back(copy);
        }
      }
      if (input->left_->type_ != kFunctionExpr) {
        auto node = get_ir_from_library(kFunctionExpr);
        if (node != empty_ir) {
          auto copy = deep_copy(input);
          deep_delete(copy->left_);
          copy->left_ = deep_copy(node);
          copy->op_->prefix_ = "";
          copy->op_->middle_ = "";
          res.push_back(copy);
        }
      }
      if (input->left_->type_ != kSelectNoParens) {
        auto node = get_ir_from_library(kSelectNoParens);
        if (node != empty_ir) {
          auto copy = deep_copy(input);
          deep_delete(copy->left_);
          copy->left_ = deep_copy(node);
          copy->op_->prefix_ = "(";
          copy->op_->middle_ = ")";
          res.push_back(copy);
        }
      }
      break;
    }
    case kCastExpr:
      /*
      CAST OP_LP expr AS type_name OP_RP
      */
      break;
    case kScalarExpr: {
      /*
      column_name
      literal
      */
      if (input->left_->type_ != kColumnName) {
        auto node = get_ir_from_library(kColumnName);
        if (node != empty_ir) {
          auto copy = deep_copy(input);
          deep_delete(copy->left_);
          copy->left_ = deep_copy(node);
          res.push_back(copy);
        }
      }
      if (input->left_->type_ != kLiteral) {
        auto node = get_ir_from_library(kLiteral);
        if (node != empty_ir) {
          auto copy = deep_copy(input);
          deep_delete(copy->left_);
          copy->left_ = deep_copy(node);
          res.push_back(copy);
        }
      }
      break;
    }
    case kUnaryExpr: {
      /*
      OP_SUB operand %prec OP_SUB
      NOT operand %prec NOT
      operand ISNULL %prec ISNULL
      operand IS NULL
      operand IS NOT NULL
      NULL
      OP_MUL
      */
      if (input->left_ != NULL) {
        res.push_back(new IR(kUnaryExpr, OP3("NULL", "", "")));
        res.push_back(new IR(kUnaryExpr, OP3("*", "", "")));

        if (input->op_->prefix_ != "-") {
          auto copy = deep_copy(input);
          copy->op_->prefix_ = "-";
          copy->op_->middle_ = "";
          res.push_back(copy);
        }
        if (input->op_->prefix_ != "NOT") {
          auto copy = deep_copy(input);
          copy->op_->prefix_ = "NOT";
          copy->op_->middle_ = "";
          res.push_back(copy);
        }
        if (input->op_->middle_ != "ISNULL") {
          auto copy = deep_copy(input);
          copy->op_->prefix_ = "";
          copy->op_->middle_ = "ISNULL";
          res.push_back(copy);
        }
        if (input->op_->middle_ != "IS NULL") {
          auto copy = deep_copy(input);
          copy->op_->prefix_ = "";
          copy->op_->middle_ = "IS NULL";
          res.push_back(copy);
        }
        if (input->op_->middle_ != "IS NOT NULL") {
          auto copy = deep_copy(input);
          copy->op_->prefix_ = "";
          copy->op_->middle_ = "IS NOT NULL";
          res.push_back(copy);
        }
      } else {
        if (input->op_->prefix_ != "NULL") {
          auto copy = deep_copy(input);
          copy->op_->prefix_ = "NULL";
          res.push_back(copy);
        } else {
          auto copy = deep_copy(input);
          copy->op_->prefix_ = "*";
          res.push_back(copy);
        }

        auto operand_node = get_ir_from_library(kOperand);
        if (operand_node != empty_ir) {
          auto tmp = new IR(input, deep_copy(operand_node), NULL);
          tmp->op_->prefix_ = "-";
          tmp->operand_num_ = 1;
          res.push_back(tmp);
          tmp = new IR(input, deep_copy(get_ir_from_library(kOperand)), NULL);
          tmp->op_->prefix_ = "NOT";
          tmp->operand_num_ = 1;
          res.push_back(tmp);
          tmp = new IR(input, deep_copy(get_ir_from_library(kOperand)), NULL);
          tmp->op_->prefix_ = "ISNULL";
          tmp->operand_num_ = 1;
          res.push_back(tmp);
          tmp = new IR(input, deep_copy(get_ir_from_library(kOperand)), NULL);
          tmp->op_->prefix_ = "IS NULL";
          tmp->operand_num_ = 1;
          res.push_back(tmp);
          tmp = new IR(input, deep_copy(get_ir_from_library(kOperand)), NULL);
          tmp->op_->prefix_ = "IS NOT NULL";
          tmp->operand_num_ = 1;
          res.push_back(tmp);
        }
      }
      break;
    }
    case kBinaryExpr: {
      /*
      comp_expr
      operand binary_op operand %prec OP_ADD
      operand LIKE operand
      operand NOT LIKE operand
      */
      if (input->right_ == NULL) {
        auto operand_node = get_ir_from_library(kOperand);
        auto binary_op_node = get_ir_from_library(kBinaryOp);
        if (operand_node != empty_ir) {
          auto tmp = new IR(kBinaryExpr, OP3("", "LIKE", ""), deep_copy(operand_node), deep_copy(get_ir_from_library(kOperand)));
          res.push_back(tmp);
          tmp = new IR(kBinaryExpr, OP3("", "NOT LIKE", ""), deep_copy(get_ir_from_library(kOperand)), deep_copy(get_ir_from_library(kOperand)));
          res.push_back(tmp);
          if (binary_op_node != empty_ir) {
            auto tmp_un = new IR(kUnknown, OP3("", "", ""), deep_copy(get_ir_from_library(kOperand)), deep_copy(binary_op_node));
            tmp = new IR(kBinaryExpr, OP3("", "", ""), tmp_un, deep_copy(get_ir_from_library(kOperand)));
            res.push_back(tmp);
          }
        }
      } else {
        auto comp_expr_node = get_ir_from_library(kCompExpr);
        if (comp_expr_node != empty_ir) {
          auto tmp = new IR(kBinaryExpr, OP3("", "", ""), deep_copy(comp_expr_node));
          res.push_back(tmp);
        }
        if (input->op_->middle_ == "") {
          auto left_with_copy = deep_copy(input->left_->left_);
          auto copy = deep_copy(input);
          deep_delete(copy->left_);
          copy->left_ = left_with_copy;
          copy->op_->middle_ = "LIKE";
          res.push_back(copy);
          copy = deep_copy(copy);
          copy->op_->middle_ = "NOT LIKE";
          res.push_back(copy);
        } else {
          auto binary_op_node = get_ir_from_library(kBinaryOp);
          if (binary_op_node != empty_ir) {
            auto operand_1_node = input->left_;
            auto operand_2_node = input->right_;
            auto tmp_un = new IR(kUnknown, OP3("", "", ""), deep_copy(operand_1_node), deep_copy(binary_op_node));
            auto tmp = new IR(kBinaryExpr, OP3("", "", ""), tmp_un, deep_copy(operand_2_node));
            res.push_back(tmp);
          }
          if (input->op_->middle_ == "LIKE") {
            auto copy = deep_copy(input);
            copy->op_->middle_ = "NOT LIKE";
            res.push_back(copy);
          } else {
            auto copy = deep_copy(input);
            copy->op_->middle_ = "LIKE";
            res.push_back(copy);
          }
        }
      }
      break;
    }
    case kLogicExpr: {
      /*
      expr AND expr
      expr OR expr
      */
      if (input->op_->middle_ != "AND") {
        auto copy = deep_copy(input);
        copy->op_->middle_ = "AND";
        res.push_back(copy);
      }
      if (input->op_->middle_ != "OR") {
        auto copy = deep_copy(input);
        copy->op_->middle_ = "OR";
        res.push_back(copy);
      }
      break;
    }
    case kInExpr: {
      /*
      operand opt_not IN OP_LP select_no_parens OP_RP
      operand opt_not IN OP_LP expr_list OP_RP
      operand opt_not IN table_name
      */
      if (input->right_->type_ != kSelectNoParens) {
        auto select_no_parens_node = get_ir_from_library(kSelectNoParens);
        if (select_no_parens_node != empty_ir) {
          auto copy = deep_copy(input);
          deep_delete(copy->right_);
          copy->right_ = deep_copy(select_no_parens_node);
          copy->op_->middle_ = "(";
          copy->op_->suffix_ = ")";
          res.push_back(copy);
        }
      }
      if (input->right_->type_ != kExprList) {
        auto expr_list_node = get_ir_from_library(kExprList);
        if (expr_list_node != empty_ir) {
          auto copy = deep_copy(input);
          deep_delete(copy->right_);
          copy->right_ = deep_copy(expr_list_node);
          copy->op_->middle_ = "(";
          copy->op_->suffix_ = ")";
          res.push_back(copy);
        }
      }
      if (input->right_->type_ != kTableName) {
        auto table_name_node = get_ir_from_library(kTableName);
        if (table_name_node != empty_ir) {
          auto copy = deep_copy(input);
          deep_delete(copy->right_);
          copy->right_ = deep_copy(table_name_node);
          copy->op_->middle_ = "";
          copy->op_->suffix_ = "";
          res.push_back(copy);
        }
      }
      break;
    }
    case kCaseExpr: {
      /*
      CASE expr case_list END
      CASE case_list END
      CASE expr case_list ELSE expr END
      CASE case_list ELSE expr END
      */
      if (input->op_->prefix_ == "CASE" && input->op_->middle_ == "" && input->op_->suffix_ == "END") {
        auto expr_1_node = input->left_;
        auto case_list_node = input->right_;
        auto expr_2_node = get_ir_from_library(kExpr);
        auto tmp = new IR(input, deep_copy(case_list_node), NULL);
        tmp->op_->middle_ = "END";
        tmp->op_->suffix_ = "";
        tmp->operand_num_ = 1;
        res.push_back(tmp);
        if (expr_2_node != empty_ir) {
          tmp = deep_copy(input);
          tmp->type_ = kUnknown;
          tmp->op_->suffix_ = "ELSE";
          tmp = new IR(kCaseExpr, OP3("", "", "END"), tmp, deep_copy(expr_2_node));
          res.push_back(tmp);
        }
        tmp = new IR(input, deep_copy(case_list_node), deep_copy(expr_1_node));
        tmp->op_->middle_ = "ELSE";
        res.push_back(tmp);
      }
      if (input->op_->prefix_ == "CASE" && input->op_->middle_ == "END" && input->op_->suffix_ == "") {
        auto case_list_node = input->left_;
        auto expr_node = get_ir_from_library(kExpr);
        if (expr_node != empty_ir) {
          auto tmp = new IR(input, deep_copy(expr_node), deep_copy(case_list_node));
          tmp->op_->middle_ = "";
          tmp->op_->suffix_ = "END";
          tmp->operand_num_ = 2;
          res.push_back(tmp);
          tmp = new IR(kUnknown, OP3("CASE", "", "ELSE"), deep_copy(get_ir_from_library(kExpr)), deep_copy(case_list_node));
          tmp = new IR(kCaseExpr, OP3("", "", "END"), tmp, deep_copy(get_ir_from_library(kExpr)));
          res.push_back(tmp);
          auto copy = deep_copy(input);
          copy->right_ = deep_copy(get_ir_from_library(kExpr));
          copy->op_->middle_ = "ELSE";
          copy->op_->suffix_ = "END";
          copy->operand_num_ = 2;
          res.push_back(copy);
        }
      }
      if (input->op_->prefix_ == "" && input->op_->middle_ == "" && input->op_->suffix_ == "END") {
        auto expr_1_node = input->left_->left_;
        auto case_list_node = input->left_->right_;
        auto expr_2_node = input->right_;
        auto copy = deep_copy(input->left_);
        copy->type_ = kCaseExpr;
        copy->op_->suffix_ = "END";
        res.push_back(copy);
        auto tmp = new IR(kCaseExpr, OP3("CASE", "END", ""), deep_copy(expr_1_node));
        res.push_back(tmp);
        tmp = new IR(kCaseExpr, OP3("CASE", "ELSE", "END"), deep_copy(case_list_node), deep_copy(expr_2_node));
        res.push_back(tmp);
      }
      if (input->op_->prefix_ == "CASE" && input->op_->middle_ == "ELSE" && input->op_->suffix_ == "END") {
        auto expr_1_node = get_ir_from_library(kExpr);
        auto case_list_node = input->left_;
        auto expr_2_node = input->right_;
        res.push_back(new IR(kCaseExpr, OP3("CASE", "END", ""), deep_copy(case_list_node)));
        if (expr_1_node != empty_ir) {
          auto tmp = new IR(kCaseExpr, OP3("CASE", "", "END"), deep_copy(expr_1_node), deep_copy(case_list_node));
          res.push_back(tmp);
          tmp = new IR(kUnknown, OP3("CASE", "", "ELSE"), deep_copy(get_ir_from_library(kExpr)), deep_copy(case_list_node));
          tmp = new IR(kCaseExpr, OP3("", "", "END"), tmp, deep_copy(expr_2_node));
          res.push_back(tmp);
        }
      }
      break;
    }
    case kBetweenExpr: {
      /*
      operand BETWEEN operand AND operand %prec BETWEEN
      operand NOT BETWEEN operand AND operand %prec NOT
      */
      if (input->left_->op_->middle_ == "BETWEEN") {
        auto copy = deep_copy(input);
        copy->left_->op_->middle_ == "NOT BETWEEN";
        res.push_back(copy);
      }
      if (input->left_->op_->middle_ == "NOT BETWEEN") {
        auto copy = deep_copy(input);
        copy->left_->op_->middle_ == "BETWEEN";
        res.push_back(copy);
      }
      break;
    }
    case kExistsExpr:
      /*
      opt_not EXISTS OP_LP select_no_parens OP_RP
      */
      break;
    case kFunctionExpr: {
      /*
      function_name OP_LP OP_RP opt_filter_clause opt_over_clause
      function_name OP_LP opt_distinct expr_list OP_RP opt_filter_clause opt_over_clause
      */
      if (input->left_->op_->middle_ == "( )") {
        auto function_name_node = input->left_->left_;
        auto opt_filter_clause_node = input->left_->right_;
        auto opt_over_clause_node = input->right_;
        auto opt_distinct_node = get_ir_from_library(kOptDistinct);
        auto expr_list_node = get_ir_from_library(kExprList);
        if (opt_distinct_node != empty_ir && expr_list_node != empty_ir) {
          auto tmp = new IR(kUnknown, OP3("", "(", ""), deep_copy(function_name_node), deep_copy(opt_distinct_node));
          tmp = new IR(kUnknown, OP3("", "", ")"), tmp, deep_copy(expr_list_node));
          tmp = new IR(kUnknown, OP3("", "", ""), tmp, deep_copy(opt_filter_clause_node));
          tmp = new IR(kFunctionExpr, OP3("", "", ""), tmp, deep_copy(opt_over_clause_node));
          res.push_back(tmp);
        }
      } else {
        auto function_name_node = input->left_->left_->left_->left_;
        auto opt_filter_clause_node = input->left_->right_;
        auto opt_over_clause_node = input->right_;
        auto tmp = new IR(kUnknown, OP3("", "( )", ""), deep_copy(function_name_node), deep_copy(opt_filter_clause_node));
        tmp = new IR(kFunctionExpr, OP3("", "", ""), tmp, deep_copy(opt_over_clause_node));
        res.push_back(tmp);
      }
      break;
    }
    case kOptDistinct: {
      /*
      DISTINCT
      (null)
      */
      if (input->op_ == NULL) {
        res.push_back(new IR(kOptDistinct, OP3("DISTINCT", "", "")));
      }
      if (input->op_ != NULL)
        res.push_back(new IR(kOptDistinct, string("")));
      break;
    }
    case kOptFilterClause: {
      /*
      FILTER OP_LP WHERE expr OP_RP
      (null)
      */
      if (input->left_ != NULL)
        res.push_back(new IR(kOptFilterClause, string("")));
      else {
        auto expr_node = get_ir_from_library(kExpr);
        if (expr_node != empty_ir) {
          auto tmp = new IR(kOptFilterClause, OP3("FILTER ( WHERE", ")", ""), deep_copy(expr_node));
          res.push_back(tmp);
        }
      }
      break;
    }
    case kOptOverClause: {
      /*
      OVER OP_LP window OP_RP
      OVER window_name
      (null)
      */
      if (input->left_ != NULL) {
        res.push_back(new IR(kOptOverClause, string("")));
        if (input->left_->type_ == kWindow) {
          auto window_name_node = get_ir_from_library(kWindowName);
          if (window_name_node != empty_ir) {
            auto copy = deep_copy(input);
            deep_delete(copy->left_);
            copy->left_ = deep_copy(window_name_node);
            copy->op_->prefix_ = "OVER";
            copy->op_->middle_ = "";
            res.push_back(copy);
          }
        } else {
          auto window_node = get_ir_from_library(kWindow);
          if (window_node != empty_ir) {
            auto copy = deep_copy(input);
            deep_delete(copy->left_);
            copy->left_ = deep_copy(window_node);
            copy->op_->prefix_ = "OVER (";
            copy->op_->middle_ = ")";
            res.push_back(copy);
          }
        }
      } else {
        auto window_name_node = get_ir_from_library(kWindowName);
        auto window_node = get_ir_from_library(kWindow);
        if (window_name_node != empty_ir) {
          auto tmp = new IR(kOptOverClause, OP3("OVER", "", ""), deep_copy(window_name_node));
          res.push_back(tmp);
        }
        if (window_node != empty_ir) {
          auto tmp = new IR(kOptOverClause, OP3("OVER (", ")", ""), deep_copy(window_node));
          res.push_back(tmp);
        }
      }
      break;
    }
    case kCaseList: {
      /*
      case_clause
      case_clause case_list
      */
      if (input->right_ == NULL) {
        auto case_list_node = get_ir_from_library(kCaseList);
        if (case_list_node != empty_ir) {
          auto tmp = new IR(input, deep_copy(input->left_), deep_copy(case_list_node));
          tmp->operand_num_ = 2;
          res.push_back(tmp);
        }
      } else {
        auto copy = deep_copy(input);
        deep_delete(copy->right_);
        copy->right_ = NULL;
        copy->operand_num_ = 1;
        res.push_back(copy);
      }
      break;
    }
    case kCaseClause:
      /*
      WHEN expr THEN expr
      */
      break;
    case kCompExpr: {
      /*
      operand OP_EQUAL operand
      operand OP_NOTEQUAL operand
      operand OP_GREATERTHAN operand
      operand OP_LESSTHAN operand
      operand OP_LESSEQ operand
      operand OP_GREATEREQ operand
      */
      if (input->op_->middle_ != "=") {
        auto copy = deep_copy(input);
        copy->op_->middle_ == "=";
        res.push_back(copy);
      }
      if (input->op_->middle_ != "!=") {
        auto copy = deep_copy(input);
        copy->op_->middle_ == "!=";
        res.push_back(copy);
      }
      if (input->op_->middle_ != ">") {
        auto copy = deep_copy(input);
        copy->op_->middle_ == ">";
        res.push_back(copy);
      }
      if (input->op_->middle_ != "<") {
        auto copy = deep_copy(input);
        copy->op_->middle_ == "<";
        res.push_back(copy);
      }
      if (input->op_->middle_ != "<=") {
        auto copy = deep_copy(input);
        copy->op_->middle_ == "<=";
        res.push_back(copy);
      }
      if (input->op_->middle_ != ">=") {
        auto copy = deep_copy(input);
        copy->op_->middle_ == ">=";
        res.push_back(copy);
      }
      break;
    }
    case kExtractExpr:
      /*
      EXTRACT OP_LP datetime_field FROM expr OP_RP
      */
      break;
    case kDatetimeField: {
      /*
      SECOND
      MINUTE
      HOUR
      DAY
      MONTH
      YEAR
      */
      if (input->op_->prefix_ != "SECOND") {
        auto copy = deep_copy(input);
        copy->op_->prefix_ = "SECOND";
        res.push_back(copy);
      }
      if (input->op_->prefix_ != "MINUTE") {
        auto copy = deep_copy(input);
        copy->op_->prefix_ = "MINUTE";
        res.push_back(copy);
      }
      if (input->op_->prefix_ != "HOUR") {
        auto copy = deep_copy(input);
        copy->op_->prefix_ = "HOUR";
        res.push_back(copy);
      }
      if (input->op_->prefix_ != "DAY") {
        auto copy = deep_copy(input);
        copy->op_->prefix_ = "DAY";
        res.push_back(copy);
      }
      if (input->op_->prefix_ != "MONTH") {
        auto copy = deep_copy(input);
        copy->op_->prefix_ = "MONTH";
        res.push_back(copy);
      }
      if (input->op_->prefix_ != "YEAR") {
        auto copy = deep_copy(input);
        copy->op_->prefix_ = "YEAR";
        res.push_back(copy);
      }
      break;
    }
    case kArrayExpr:
      /*
      ARRAY OP_LBRACKET expr_list OP_RBRACKET
      */
      break;
    case kArrayIndex:
      /*
      operand OP_LBRACKET int_literal OP_RBRACKET
      */
      break;
    case kLiteral: {
      /*
      string_literal
      bool_literal
      num_literal
      */
      if (input->left_->type_ != kStringLiteral) {
        auto string_literal_node = get_ir_from_library(kStringLiteral);
        if (string_literal_node != empty_ir) {
          auto copy = deep_copy(input);
          deep_delete(copy->left_);
          copy->left_ = deep_copy(string_literal_node);
          res.push_back(copy);
        }
      }
      if (input->left_->type_ != kBoolLiteral) {
        auto bool_literal_node = get_ir_from_library(kBoolLiteral);
        if (bool_literal_node != empty_ir) {
          auto copy = deep_copy(input);
          deep_delete(copy->left_);
          copy->left_ = deep_copy(bool_literal_node);
          res.push_back(copy);
        }
      }
      if (input->left_->type_ != kNumLiteral) {
        auto num_literal_node = get_ir_from_library(kNumLiteral);
        if (num_literal_node != empty_ir) {
          auto copy = deep_copy(input);
          deep_delete(copy->left_);
          copy->left_ = deep_copy(num_literal_node);
          res.push_back(copy);
        }
      }
      break;
    }
    case kBoolLiteral: {
      /*
      TRUE
      FALSE
      */
      if (input->op_->prefix_ != "TRUE") {
        auto copy = deep_copy(input);
        copy->op_->prefix_ = "TRUE";
        res.push_back(copy);
      }
      if (input->op_->prefix_ != "FALSE") {
        auto copy = deep_copy(input);
        copy->op_->prefix_ = "FALSE";
        res.push_back(copy);
      }
      break;
    }
    case kNumLiteral: {
      /*
      int_literal
      float_literal
      */
      if (input->left_->type_ != kIntLiteral) {
        auto int_literal_node = get_ir_from_library(kIntLiteral);
        if (int_literal_node != empty_ir) {
          auto copy = deep_copy(input);
          deep_delete(copy->left_);
          copy->left_ = deep_copy(int_literal_node);
          res.push_back(copy);
        }
      }
      if (input->left_->type_ != kFloatLiteral) {
        auto float_literal_node = get_ir_from_library(kFloatLiteral);
        if (float_literal_node != empty_ir) {
          auto copy = deep_copy(input);
          deep_delete(copy->left_);
          copy->left_ = deep_copy(float_literal_node);
          res.push_back(copy);
        }
      }
      break;
    }
    case kOptColumn: {
      /*
      COLUMN
      (null)
      */
      if (input->op_ == NULL) {
        res.push_back(new IR(kOptColumn, OP3("COLUMN", "", "")));
      }
      if (input->op_ != NULL)
        res.push_back(new IR(kOptColumn, string("")));
      break;
    }
    case kTriggerBody: {
      /*
      drop_stmt
      update_stmt
      isnert_stmt
      alter_stmt
      */
      if (input->left_->type_ != kDropStmt) {
        auto drop_stmt_node = get_ir_from_library(kDropStmt);
        if (drop_stmt_node != empty_ir) {
          auto copy = deep_copy(input);
          deep_delete(copy->left_);
          copy->left_ = deep_copy(drop_stmt_node);
          res.push_back(copy);
        }
      }
      if (input->left_->type_ != kUpdateStmt) {
        auto update_stmt_node = get_ir_from_library(kUpdateStmt);
        if (update_stmt_node != empty_ir) {
          auto copy = deep_copy(input);
          deep_delete(copy->left_);
          copy->left_ = deep_copy(update_stmt_node);
          res.push_back(copy);
        }
      }
      if (input->left_->type_ != kInsertStmt) {
        auto insert_stmt_node = get_ir_from_library(kInsertStmt);
        if (insert_stmt_node != empty_ir) {
          auto copy = deep_copy(input);
          deep_delete(copy->left_);
          copy->left_ = deep_copy(insert_stmt_node);
          res.push_back(copy);
        }
      }
      if (input->left_->type_ != kAlterStmt) {
        auto alter_stmt_node = get_ir_from_library(kAlterStmt);
        if (alter_stmt_node != empty_ir) {
          auto copy = deep_copy(input);
          deep_delete(copy->left_);
          copy->left_ = deep_copy(alter_stmt_node);
          res.push_back(copy);
        }
      }
      break;
    }
    case kOptIfNotExist: {
      /*
      IF NOT EXISTS
      (null)
      */
      if (input->op_ == NULL) {
        res.push_back(new IR(kOptIfNotExist, OP3("IF NOT EXISTS", "", "")));
      }
      if (input->op_ != NULL)
        res.push_back(new IR(kOptIfNotExist, string("")));
      break;
    }
    case kOptIfExist: {
      /*
      IF EXISTS
      (null)
      */
      if (input->op_ == NULL) {
        res.push_back(new IR(kOptIfExist, OP3("IF EXISTS", "", "")));
      }
      if (input->op_ != NULL)
        res.push_back(new IR(kOptIfExist, string("")));
      break;
    }
    case kAsAlias: {
      /*
      identifier
      */
      for (auto node : res) {
        node->left_->data_type_ = kDataAliasName;
        node->left_->scope_ = 1;
        node->left_->data_flag_ = kDefine;
      }
      break;
    }
    case kTableName: {
      /*
      identifier
      */
      for (auto node : res) {
        node->left_->data_type_ = kDataTableName;
        node->left_->scope_ = 1;
        node->left_->data_flag_ = kUse;
      }
      break;
    }
    case kColumnName: {
      /*
      identifier
      */
      for (auto node : res) {
        node->left_->data_type_ = kDataColumnName;
        node->left_->scope_ = 2;
        node->left_->data_flag_ = kUse;
      }
      break;
    }
    case kOptIndexKeyword: {
      /*
      UNIQUE
      FULLTEXT
      SPATIAL
      (null)
      */
      if (input->op_ == NULL || input->op_->prefix_ != "UNIQUE") {
        if (input->op_) {
          auto copy = deep_copy(input);
          copy->op_->prefix_ = "UNIQUE";
          res.push_back(copy);
        } else {
          res.push_back(new IR(kOptIndexKeyword, OP3("UNIQUE", "", "")));
        }
      }
      if (input->op_ == NULL || input->op_->prefix_ != "FULLTEXT") {
        if (input->op_) {
          auto copy = deep_copy(input);
          copy->op_->prefix_ = "FULLTEXT";
          res.push_back(copy);
        } else {
          res.push_back(new IR(kOptIndexKeyword, OP3("FULLTEXT", "", "")));
        }
      }
      if (input->op_ == NULL || input->op_->prefix_ != "SPATIAL") {
        if (input->op_) {
          auto copy = deep_copy(input);
          copy->op_->prefix_ = "SPATIAL";
          res.push_back(copy);
        } else {
          res.push_back(new IR(kOptIndexKeyword, OP3("SPATIAL", "", "")));
        }
      }
      if (input->op_ != NULL)
        res.push_back(new IR(kOptIndexKeyword, string("")));
      break;
    }
    case kFunctionName: {
      /*
      identifier
      */
      for (auto node : res) {
        node->left_->data_type_ = kDataFunctionName;
        node->left_->scope_ = 1;
        node->left_->data_flag_ = kGlobal;
      }
      break;
    }
    case kBinaryOp: {
      /*
      OP_ADD
      OP_SUB
      OP_DIVIDE
      OP_MOD
      OP_MUL
      OP_XOR
      */
      if (input->op_->prefix_ != "+") {
        auto copy = deep_copy(input);
        copy->op_->prefix_ = "+";
        res.push_back(copy);
      }
      if (input->op_->prefix_ != "-") {
        auto copy = deep_copy(input);
        copy->op_->prefix_ = "-";
        res.push_back(copy);
      }
      if (input->op_->prefix_ != "/") {
        auto copy = deep_copy(input);
        copy->op_->prefix_ = "/";
        res.push_back(copy);
      }
      if (input->op_->prefix_ != "%") {
        auto copy = deep_copy(input);
        copy->op_->prefix_ = "%";
        res.push_back(copy);
      }
      if (input->op_->prefix_ != "*") {
        auto copy = deep_copy(input);
        copy->op_->prefix_ = "*";
        res.push_back(copy);
      }
      if (input->op_->prefix_ != "^") {
        auto copy = deep_copy(input);
        copy->op_->prefix_ = "^";
        res.push_back(copy);
      }
      break;
    }
    case kOptNot: {
      /*
      NOT
      (null)
      */
      if (input->op_ == NULL) {
        res.push_back(new IR(kOptNot, OP3("NOT", "", "")));
      }
      if (input->op_ != NULL)
        res.push_back(new IR(kOptNot, string("")));
      break;
    }
    case kTypeName: {
      /*
      numeric_type
      character_type
      */
      if (input->left_->type_ != kNumericType) {
        auto numeric_type_node = get_ir_from_library(kNumericType);
        if (numeric_type_node != empty_ir) {
          auto copy = deep_copy(input);
          deep_delete(copy->left_);
          copy->left_ = deep_copy(numeric_type_node);
          res.push_back(copy);
        }
      }
      if (input->left_->type_ != kCharacterType) {
        auto character_type_node = get_ir_from_library(kCharacterType);
        if (character_type_node != empty_ir) {
          auto copy = deep_copy(input);
          deep_delete(copy->left_);
          copy->left_ = deep_copy(character_type_node);
          res.push_back(copy);
        }
      }
      break;
    }
    case kCharacterType: {
      /*
      character_with_length
      character_without_length
      */
      if (input->left_->type_ != kCharacterWithLength) {
        auto character_with_length_node = get_ir_from_library(kCharacterWithLength);
        if (character_with_length_node != empty_ir) {
          auto copy = deep_copy(input);
          deep_delete(copy->left_);
          copy->left_ = deep_copy(character_with_length_node);
          res.push_back(copy);
        }
      }
      if (input->left_->type_ != kCharacterType) {
        auto character_type_node = get_ir_from_library(kCharacterType);
        if (character_type_node != empty_ir) {
          auto copy = deep_copy(input);
          deep_delete(copy->left_);
          copy->left_ = deep_copy(character_type_node);
          res.push_back(copy);
        }
      }
      break;
    }
    case kCharacterWithLength:
      /*
      character_conflicta OP_LP int_literal OP_RP
      */
      break;
    case kCharacterWithoutLength: {
      /*
      character_conflicta
      SET
      ENUM
      BINARY
      */
      if (input->left_ != NULL) {
        res.push_back(new IR(kCharacterWithoutLength, OP3("SET", "", "")));
        res.push_back(new IR(kCharacterWithoutLength, OP3("ENUM", "", "")));
        res.push_back(new IR(kCharacterWithoutLength, OP3("BINARY", "", "")));
      } else {
        auto character_conflicta_node = get_ir_from_library(kCharacterConflicta);
        if (character_conflicta_node != empty_ir) {
          auto tmp = new IR(kCharacterWithoutLength, OP3("", "", ""), deep_copy(character_conflicta_node));
          res.push_back(tmp);
        }
        if (input->op_->prefix_ != "SET") {
          auto copy = deep_copy(input);
          copy->op_->prefix_ = "SET";
          res.push_back(copy);
        }
        if (input->op_->prefix_ != "ENUM") {
          auto copy = deep_copy(input);
          copy->op_->prefix_ = "ENUM";
          res.push_back(copy);
        }
        if (input->op_->prefix_ != "BINARY") {
          auto copy = deep_copy(input);
          copy->op_->prefix_ = "BINARY";
          res.push_back(copy);
        }
      }
      break;
    }
    case kCharacterConflicta: {
      /*
      CHARACTER
      CHAR
      VARCHAR
      TEXT
      TINYTEXT
      MEDIUMTEXT
      LONGTEXT
      NATIONAL CHARACTER
      NATIONAL CHAR
      NCHAR
      */
      if (input->op_->prefix_ != "CHARACTER") {
        auto copy = deep_copy(input);
        copy->op_->prefix_ = "CHARACTER";
        res.push_back(copy);
      }
      if (input->op_->prefix_ != "CHAR") {
        auto copy = deep_copy(input);
        copy->op_->prefix_ = "CHAR";
        res.push_back(copy);
      }
      if (input->op_->prefix_ != "VARCHAR") {
        auto copy = deep_copy(input);
        copy->op_->prefix_ = "VARCHAR";
        res.push_back(copy);
      }
      if (input->op_->prefix_ != "TEXT") {
        auto copy = deep_copy(input);
        copy->op_->prefix_ = "TEXT";
        res.push_back(copy);
      }
      if (input->op_->prefix_ != "TINYTEXT") {
        auto copy = deep_copy(input);
        copy->op_->prefix_ = "TINYTEXT";
        res.push_back(copy);
      }
      if (input->op_->prefix_ != "MEDIUMTEXT") {
        auto copy = deep_copy(input);
        copy->op_->prefix_ = "MEDIUMTEXT";
        res.push_back(copy);
      }
      if (input->op_->prefix_ != "LONGTEXT") {
        auto copy = deep_copy(input);
        copy->op_->prefix_ = "LONGTEXT";
        res.push_back(copy);
      }
      if (input->op_->prefix_ != "NATIONAL CHARACTER") {
        auto copy = deep_copy(input);
        copy->op_->prefix_ = "NATIONAL CHARACTER";
        res.push_back(copy);
      }
      if (input->op_->prefix_ != "NATIONAL CHAR") {
        auto copy = deep_copy(input);
        copy->op_->prefix_ = "NATIONAL CHAR";
        res.push_back(copy);
      }
      if (input->op_->prefix_ != "NCHAR") {
        auto copy = deep_copy(input);
        copy->op_->prefix_ = "NCHAR";
        res.push_back(copy);
      }
      break;
    }
    case kNumericType: {
      /*
      INT
      INTEGER
      SMALLINT
      BIGINT
      REAL
      FLOAT
      FIXED
      DOUBLE
      DOUBLE PRECISION
      DECIMAL
      DEC
      NUMERIC
      BOOLEAN
      */
      if (input->op_->prefix_ != "INT") {
        auto copy = deep_copy(input);
        copy->op_->prefix_ = "INT";
        res.push_back(copy);
      }
      if (input->op_->prefix_ != "INTEGER") {
        auto copy = deep_copy(input);
        copy->op_->prefix_ = "INTEGER";
        res.push_back(copy);
      }
      if (input->op_->prefix_ != "SMALLINT") {
        auto copy = deep_copy(input);
        copy->op_->prefix_ = "SMALLINT";
        res.push_back(copy);
      }
      if (input->op_->prefix_ != "BIGINT") {
        auto copy = deep_copy(input);
        copy->op_->prefix_ = "BIGINT";
        res.push_back(copy);
      }
      if (input->op_->prefix_ != "REAL") {
        auto copy = deep_copy(input);
        copy->op_->prefix_ = "REAL";
        res.push_back(copy);
      }
      if (input->op_->prefix_ != "FLOAT") {
        auto copy = deep_copy(input);
        copy->op_->prefix_ = "FLOAT";
        res.push_back(copy);
      }
      if (input->op_->prefix_ != "FIXED") {
        auto copy = deep_copy(input);
        copy->op_->prefix_ = "FIXED";
        res.push_back(copy);
      }
      if (input->op_->prefix_ != "DOUBLE") {
        auto copy = deep_copy(input);
        copy->op_->prefix_ = "DOUBLE";
        res.push_back(copy);
      }
      if (input->op_->prefix_ != "DOUBLE PRECISION") {
        auto copy = deep_copy(input);
        copy->op_->prefix_ = "DOUBLE PRECISION";
        res.push_back(copy);
      }
      if (input->op_->prefix_ != "DECIMAL") {
        auto copy = deep_copy(input);
        copy->op_->prefix_ = "DECIMAL";
        res.push_back(copy);
      }
      if (input->op_->prefix_ != "DEC") {
        auto copy = deep_copy(input);
        copy->op_->prefix_ = "DEC";
        res.push_back(copy);
      }
      if (input->op_->prefix_ != "NUMERIC") {
        auto copy = deep_copy(input);
        copy->op_->prefix_ = "NUMERIC";
        res.push_back(copy);
      }
      if (input->op_->prefix_ != "BOOLEAN") {
        auto copy = deep_copy(input);
        copy->op_->prefix_ = "BOOLEAN";
        res.push_back(copy);
      }
      break;
    }
    case kOptTableConstraintList: {
      /*
      table_constraint_list
      (null)
      */
      if (input->left_ != NULL)
        res.push_back(new IR(kOptTableConstraintList, string("")));
      else {
        auto table_constraint_list_node = get_ir_from_library(kTableConstraintList);
        if (table_constraint_list_node != empty_ir) {
          auto tmp = new IR(kOptTableConstraintList, OP3("", "", ""), deep_copy(table_constraint_list_node));
          res.push_back(tmp);
        }
      }
      break;
    }
    case kTableConstraintList: {
      /*
      table_constraint
      table_constraint OP_COMMA table_constraint_list
      */
      if (input->right_ == NULL) {
        auto table_constraint_list_node = get_ir_from_library(kTableConstraintList);
        if (table_constraint_list_node != empty_ir) {
          auto tmp = new IR(input, deep_copy(input->left_), deep_copy(table_constraint_list_node));
          tmp->operand_num_ = 2;
          tmp->op_->middle_ = ",";
          res.push_back(tmp);
        }
      } else {
        auto copy = deep_copy(input);
        deep_delete(copy->right_);
        copy->right_ = NULL;
        copy->operand_num_ = 1;
        copy->op_->middle_ = "";
        res.push_back(copy);
      }
      break;
    }
    case kTableConstraint: {
      /*
      constraint_name PRIMARY KEY OP_LP indexed_column_list OP_RP
      constraint_name UNIQUE OP_LP indexed_column_list OP_RP
      constraint_name CHECK OP_LP expr OP_RP opt_enforced
      constraint_name FOREIGN KEY OP_LP column_name_list OP_RP reference_clause
      */
      if (input->op_->middle_ == "PRIMARY KEY (") {
        auto copy = deep_copy(input);
        copy->op_->middle_ = "UNIQUE (";
        res.push_back(copy);
        auto reference_clause_node = get_ir_from_library(kReferenceClause);
        if (reference_clause_node != empty_ir) {
          copy = deep_copy(input);
          copy->type_ = kUnknown;
          copy->op_->middle_ = "FOREIGN KEY (";
          auto tmp = new IR(kTableConstraint, OP3("", "", ""), copy, deep_copy(reference_clause_node));
          res.push_back(tmp);
        }
        auto expr_node = get_ir_from_library(kExpr);
        auto opt_enforced_node = get_ir_from_library(kOptEnforced);
        if (expr_node != empty_ir && opt_enforced_node != empty_ir) {
          auto constraint_name_node = input->left_;
          auto tmp = new IR(kUnknown, OP3("", "CHECK (", ")"), deep_copy(constraint_name_node), deep_copy(expr_node));
          tmp = new IR(kTableConstraint, OP3("", "", ""), tmp, deep_copy(opt_enforced_node));
          res.push_back(tmp);
        }
      }
      if (input->op_->middle_ == "UNIQUE (") {
        auto copy = deep_copy(input);
        copy->op_->middle_ = "PRIMARY KEY (";
        res.push_back(copy);
        auto reference_clause_node = get_ir_from_library(kReferenceClause);
        if (reference_clause_node != empty_ir) {
          copy = deep_copy(input);
          copy->type_ = kUnknown;
          copy->op_->middle_ = "FOREIGN KEY (";
          auto tmp = new IR(kTableConstraint, OP3("", "", ""), copy, deep_copy(reference_clause_node));
          res.push_back(tmp);
        }
        auto expr_node = get_ir_from_library(kExpr);
        auto opt_enforced_node = get_ir_from_library(kOptEnforced);
        if (expr_node != empty_ir && opt_enforced_node != empty_ir) {
          auto constraint_name_node = input->left_;
          auto tmp = new IR(kUnknown, OP3("", "CHECK (", ")"), deep_copy(constraint_name_node), deep_copy(expr_node));
          tmp = new IR(kTableConstraint, OP3("", "", ""), tmp, deep_copy(opt_enforced_node));
          res.push_back(tmp);
        }
      }
      if (input->op_->middle_ == "") {
        auto constraint_name_node = input->left_->left_;
        auto indexed_column_list_node = get_ir_from_library(kIndexedColumnList);
        if (indexed_column_list_node != empty_ir) {
          auto tmp = new IR(input, deep_copy(constraint_name_node), deep_copy(indexed_column_list_node));
          tmp->op_->middle_ = "PRIMARY KEY (";
          tmp->op_->suffix_ = ")";
          res.push_back(tmp);
          tmp = new IR(input, deep_copy(constraint_name_node), deep_copy(get_ir_from_library(kIndexedColumnList)));
          tmp->op_->middle_ = "UNIQUE (";
          tmp->op_->suffix_ = ")";
          res.push_back(tmp);
        }
        if (input->left_->op_->middle_ == "CHECK (") {
          auto column_name_list_node = get_ir_from_library(kColumnNameList);
          auto reference_clause_node = get_ir_from_library(kReferenceClause);
          if (column_name_list_node != empty_ir && reference_clause_node != empty_ir) {
            auto copy = deep_copy(input);
            deep_delete(copy->left_->right_);
            copy->left_->right_ = deep_copy(column_name_list_node);
            deep_delete(copy->right_);
            copy->right_ = deep_copy(reference_clause_node);
            copy->left_->op_->middle_ = "FOREIGN KEY (";
            res.push_back(copy);
          }
        } else { // input->left_->op_->middle_ == "FOREIGN KEY ("
          auto expr_node = get_ir_from_library(kExpr);
          auto opt_enforced_node = get_ir_from_library(kOptEnforced);
          if (expr_node != empty_ir && opt_enforced_node != empty_ir) {
            auto copy = deep_copy(input);
            deep_delete(copy->left_->right_);
            copy->left_->right_ = deep_copy(expr_node);
            deep_delete(copy->right_);
            copy->right_ = deep_copy(opt_enforced_node);
            copy->left_->op_->middle_ = "CHECK (";
            res.push_back(copy);
          }
        }
      }
      for (auto node : res) {
        if (node->right_->type_ != kReferenceClause)
          continue;
        auto column_name_list_node = node->left_->right_;
        while (column_name_list_node) {
          auto identifier_node = column_name_list_node->left_->left_;
          identifier_node->data_type_ = kDataColumnName;
          identifier_node->scope_ = 2;
          identifier_node->data_flag_ = kUse;
          column_name_list_node = column_name_list_node->right_;
        }
      }
      break;
    }
    case kOptEnforced: {
      /*
      ENFORCED
      NOT ENFORCED
      (null)
      */
      if (input->op_ == NULL || input->op_->prefix_ != "ENFORCED") {
        if (input->op_) {
          auto copy = deep_copy(input);
          copy->op_->prefix_ = "ENFORCED";
          res.push_back(copy);
        } else {
          res.push_back(new IR(kOptEnforced, OP3("ENFORCED", "", "")));
        }
      }
      if (input->op_ == NULL || input->op_->prefix_ != "NOT ENFORCED") {
        if (input->op_) {
          auto copy = deep_copy(input);
          copy->op_->prefix_ = "NOT ENFORCED";
          res.push_back(copy);
        } else {
          res.push_back(new IR(kOptEnforced, OP3("NOT ENFORCED", "", "")));
        }
      }
      if (input->op_ != NULL)
        res.push_back(new IR(kOptEnforced, string("")));
      break;
    }
    default:
      break;
  }

  input->mutated_times_ += res.size();
  for (auto i : res) {
    if (i == NULL) continue;
    i->mutated_times_ = input->mutated_times_;
  }
  return res;
}

