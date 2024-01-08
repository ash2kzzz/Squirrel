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

// Number of each node type in library
#define NUMOFNT 100

using namespace std;

vector<string> Mutator::common_string_libary;
vector<unsigned long> Mutator::value_libary;
map<string, vector<string>> Mutator::m_tables;
vector<string> Mutator::v_table_names;

vector<IRTYPE> candidate_type_statement = {kSelectStatement,
                                            kImportStatement,
                                            kCreateStatement,
                                            kInsertStatement,
                                            kDeleteStatement,
                                            kUpdateStatement,
                                            kDropStatement,
                                            kExecuteStatement,
                                            kAlterStatement,
                                            kPrepareStatement};

vector<IRTYPE> candidate_type_cmd = {kCmdPragma,
                                      kCmdReindex,
                                      kCmdAnalyze,
                                      kCmdAttach,
                                      kCmdDetach,
                                      kCmdRelease,
                                      kRollbackStatement,
                                      kVacuumStatement,
                                      kBeginStatement,
                                      kCommitStatement};

vector<IRTYPE> candidate_type_expr = {kOperand,
                                      kBetweenExpr,
                                      kLogicExpr,
                                      kExistsExpr,
                                      kInExpr,
                                      kCastExpr};

vector<IRTYPE> candidate_type_operand_case1 = {kArrayIndex,
                                               kScalarExpr,
                                               kUnaryExpr,
                                               kBinaryExpr,
                                               kCaseExpr,
                                               kFunctionExpr,
                                               kExtractExpr,
                                               kArrayExpr};

vector<IRTYPE> candidate_type_literal = {kStringLiteral,
                                         kBoolLiteral,
                                         kNumLiteral,
                                         kNullLiteral,
                                         kParamExpr};


IR *Mutator::deep_copy_with_record(const IR *root, const IR *record) {
  IR *left = NULL, *right = NULL, *copy_res;

  if (root->left_)
    left = deep_copy_with_record(
        root->left_, record);  // do you have a second version for deep_copy
                               // that accept only one argument?
  if (root->right_)
    right = deep_copy_with_record(root->right_,
                                  record);  // no I forget to update here

  if (root->op_ != NULL)
    copy_res = new IR(
        root->type_,
        OP3(root->op_->prefix_, root->op_->middle_, root->op_->suffix_), left,
        right, root->f_val_, root->str_val_, root->name_, root->mutated_times_);
  else
    copy_res = new IR(root->type_, NULL, left, right, root->f_val_,
                      root->str_val_, root->name_, root->mutated_times_);

  copy_res->id_type_ = root->id_type_;

  if (root == record && record != NULL) {
    this->record_ = copy_res;
  }

  return copy_res;
}

bool Mutator::check_node_num(IR *root, unsigned int limit) {
  auto v_statements = extract_statement(root);
  bool is_good = true;

  if (v_statements.size() > 5) {
    is_good = false;

  } else
    for (auto stmt : v_statements) {
      if (calc_node(stmt) > limit) {
        is_good = false;
        break;
      }
    }

  return is_good;
}

vector<IR *> Mutator::mutate_all(vector<IR *> &v_ir_collector) {
  vector<IR *> res;
  set<unsigned long> res_hash;
  IR *root = v_ir_collector[v_ir_collector.size() - 1];
  res_hash.insert(hash(extract_struct(root)));

  for (auto ir : v_ir_collector) {
    if (ir == root || ir->type_ == kProgram) continue;
    if (ir->type_ == kUnknown) continue;
    if (ir->type_ == kPreparableStatement || ir->type_ == kCmd) continue;
    if (identifier_type.find(ir->type_) != identifier_type.end()) continue;
    if (single_grammar_expression.find(ir->type_) != single_grammar_expression.end()) continue;
    if (list_type.find(ir->type_) != list_type.end()) continue;
    // vector<IR *> v_mutated_ir = mutate(ir);
    vector<IR *> v_mutated_ir = mutate2(ir);

    for (auto i : v_mutated_ir) {
      IR *new_ir_tree = deep_copy_with_record(root, ir);
      replace(new_ir_tree, this->record_, i);

      if (!check_node_num(new_ir_tree, 100)) {
        deep_delete(new_ir_tree);
        continue;
      }

      string tmp = extract_struct(new_ir_tree);
      unsigned tmp_hash = hash(tmp);
      if (res_hash.find(tmp_hash) != res_hash.end()) {
        deep_delete(new_ir_tree);
        continue;
      }

      res_hash.insert(tmp_hash);
      res.push_back(new_ir_tree);
    }
  }

  return res;
}

vector<IR *> Mutator::mutate2(IR *input) {
  vector<IR *> res;

  if (!lucky_enough_to_be_mutated(input->mutated_times_)) {
    return res;  // return a empty set if the IR is not mutated
  }

  switch (input->type_)
  {
  // case kStatementList: {
  //   auto copy = deep_copy(input);
  //   int size = left_lib[kStatementList].size();
  //   auto new_right = deep_copy(left_lib[kStatementList][get_rand_int(size)]);
  //   auto new_res = new IR(kStatementList, OPMID(";"), copy, new_right);
  //   res.push_back(new_res);
  //   break;
  // }
  case kStatement: {
    /*
    prepare_statement opt_hints
    preparable_statement(select_statement/import_statement/...) opt_hints
    show_statement
    cmd
    */
    if (input->right_) {
      auto new_ir = get_from_libary_2D_type(candidate_type_statement[get_rand_int(candidate_type_statement.size())]);
      if (new_ir) {
        auto copy = deep_copy(input);
        auto left = copy->left_;
        copy->left_ = deep_copy(new_ir);
        deep_delete(left);
        res.push_back(copy);
      }
    } else {
      auto type = input->left_->type_;
      auto new_ir = get_from_libary_2D_type(type == kShowStatement ? candidate_type_cmd[get_rand_int(candidate_type_cmd.size())] : kShowStatement);
      if (new_ir) {
        auto copy = deep_copy(input);
        auto left = copy->left_;
        copy->left_ = deep_copy(new_ir);
        deep_delete(left);
        res.push_back(copy);
      }
    }
    break;
  }
  case kCmdRelease: {
    /*
    RELEASE SAVEPOINT savepoint_name
    RELEASE savepoint_name
    */
    if (input->op_->prefix_ != "RELEASE SAVEPOINT") {
      auto copy = deep_copy(input);
      copy->op_->prefix_ = "RELEASE SAVEPOINT";
      res.push_back(copy);
    }
    if (input->op_->prefix_ != "RELEASE") {
      auto copy = deep_copy(input);
      copy->op_->prefix_ = "RELEASE";
      res.push_back(copy);
    }
    break;
  }
  case kCmdPragma: {
    /*
    PRAGMA pragma_key
    PRAGMA pragma_key '=' pragma_value
    PRAGMA pragma_key '(' pragma_value ')'
    */
    if (input->right_ != NULL) {
      auto copy = deep_copy(input);
      deep_delete(copy->right_);
      copy->right_ = NULL;
      copy->op_->middle_ = "";
      copy->op_->suffix_ = "";
      copy->operand_num_ = 1;
      res.push_back(copy);
    }
    if (input->op_->middle_ != "=") {
      if (input->right_ == NULL) {
        auto new_ir = get_from_libary_2D_type(kPragmaValue);
        if (new_ir) {
          auto copy = deep_copy(input);
          copy->right_ = deep_copy(new_ir);
          copy->op_->middle_ = "=";
          copy->operand_num_ = 2;
          res.push_back(copy);
        }
      } else {
        auto copy = deep_copy(input);
        copy->op_->middle_ = "=";
        copy->op_->suffix_ = "";
        copy->operand_num_ = 2;
        res.push_back(copy);
      }
    }
    if (input->op_->middle_ != "(") {
      if (input->right_ == NULL) {
        auto new_ir = get_from_libary_2D_type(kPragmaValue);
        if (new_ir) {
          auto copy = deep_copy(input);
          copy->right_ = deep_copy(new_ir);
          copy->op_->middle_ = "(";
          copy->op_->suffix_ = ")";
          copy->operand_num_ = 2;
          res.push_back(copy);
        }
      } else {
        auto copy = deep_copy(input);
        copy->op_->middle_ = "(";
        copy->op_->suffix_ = ")";
        copy->operand_num_ = 2;
        res.push_back(copy);
      }
    }
    break;
  }
  case kCmdReindex: {
    /*
    REINDEX
    REINDEX table_name
    */
    if (input->left_ == NULL) {
      auto new_ir = get_from_libary_2D_type(kTableName);
      if (new_ir) {
        auto copy = deep_copy(input);
        copy->str_val_ = "";
        copy->op_ = OP1("REINDEX");
        copy->left_ = deep_copy(new_ir);
        copy->operand_num_ = 1;
        if (copy->left_->right_ == NULL) {
          copy->left_->left_->id_type_ = id_top_table_name;
         } else {
          copy->left_->right_->id_type_ = id_top_table_name;
         }
         res.push_back(copy);
      }
    } else {
      auto copy = deep_copy(input);
      copy->str_val_ = "REINDEX";
      delete copy->op_;
      copy->op_ = NULL;
      deep_delete(copy->left_);
      copy->left_ = NULL;
      copy->operand_num_ = 0;
      res.push_back(copy);
    }
    break;
  }
  case kCmdAnalyze: {
    /*
    ANALYZE
    ANALYZE table_name
    */
    if (input->left_ == NULL) {
      auto new_ir = get_from_libary_2D_type(kTableName);
      if (new_ir) {
        auto copy = deep_copy(input);
        copy->str_val_ = "";
        copy->op_ = OP1("ANALYZE");
        copy->left_ = deep_copy(new_ir);
        copy->operand_num_ = 1;
        if (copy->left_->right_ == NULL) {
          copy->left_->left_->id_type_ = id_top_table_name;
         } else {
          copy->left_->right_->id_type_ = id_top_table_name;
         }
         res.push_back(copy);
      }
    } else {
      auto copy = deep_copy(input);
      copy->str_val_ = "ANALYZE";
      delete copy->op_;
      copy->op_ = NULL;
      deep_delete(copy->left_);
      copy->left_ = NULL;
      copy->operand_num_ = 0;
      res.push_back(copy);
    }
    break;
  }
  case kCmdAttach: {
    /*
    ATTACH expr AS schema_name
    ATTACH DATABASE expr AS schema_name
    */
    if (input->op_->prefix_ != "ATTACH") {
      auto copy = deep_copy(input);
      copy->op_->prefix_ = "ATTACH";
      res.push_back(copy);
    }
    if (input->op_->prefix_ != "ATTACH DATABASE") {
      auto copy = deep_copy(input);
      copy->op_->prefix_ = "ATTACH DATABASE";
      res.push_back(copy);
    }
    break;
  }
  case kCmdDetach: {
    /*
    DETACH schema_name
    DETACH DATABASE schema_name
    */
    if (input->op_->prefix_ != "DETACH") {
      auto copy = deep_copy(input);
      copy->op_->prefix_ = "DETACH";
      res.push_back(copy);
    }
    if (input->op_->prefix_ != "DETACH DATABASE") {
      auto copy = deep_copy(input);
      copy->op_->prefix_ = "DETACH DATABASE";
      res.push_back(copy);
    }
    break;
  }
  case kPragmaKey: {
    /*
    pragma_name
    schema_name '.' pragma_name
    */
    if (input->right_ == NULL) {
      auto new_ir = get_from_libary_2D_type(kSchemaName);
      if (new_ir) {
        auto copy = deep_copy(input);
        auto pragma_name = copy->left_;
        copy->left_ = deep_copy(new_ir);
        copy->right_ = pragma_name;
        copy->op_->middle_ = ".";
        copy->operand_num_ = 2;
        res.push_back(copy);
      }
    } else {
      auto copy = deep_copy(input);
      auto pragma_name = copy->right_;
      copy->right_ = NULL;
      deep_delete(copy->left_);
      copy->left_ = pragma_name;
      copy->op_->middle_ = "";
      copy->operand_num_ = 1;
      res.push_back(copy);
    }
    break;
  }
  case kPragmaValue: {
    /*
    num_literal
    string_literal
    IDENTIFIER
    ON
    DELETE
    DEFAULT
    */
    if (input->left_->type_ != kNumLiteral) {
      auto new_ir = get_from_libary_2D_type(kNumLiteral);
      if (new_ir) {
        auto copy = deep_copy(input);
        deep_delete(copy->left_);
        copy->left_ = deep_copy(new_ir);
        res.push_back(copy);
      }
    }
    if (input->left_->type_ != kStringLiteral) {
      auto new_ir = get_from_libary_2D_type(kStringLiteral);
      if (new_ir) {
        auto copy = deep_copy(input);
        deep_delete(copy->left_);
        copy->left_ = deep_copy(new_ir);
        res.push_back(copy);
      }
    }
    if (input->left_->type_ != kIdentifier) {
      auto new_ir = get_from_libary_2D_type(kIdentifier);
      if (new_ir) {
        auto copy = deep_copy(input);
        deep_delete(copy->left_);
        copy->left_ = deep_copy(new_ir);
        copy->left_->id_type_ = id_pragma_value;
        res.push_back(copy);
      }
    }
    break;
  }
  case kOptTransaction: {
    /*
    TRANSACTION
    (null)
    */
    if (input->str_val_ != "TRANSACTION") {
      auto copy = deep_copy(input);
      copy->str_val_ = "TRANSACTION";
      res.push_back(copy);
    }
    if (input->str_val_ != "") {
      auto copy = deep_copy(input);
      copy->str_val_ = "";
      res.push_back(copy);
    }
    break;
  }
  case kOptToSavepoint: {
    /*
    TO savepoint_name
    TO SAVEPOINT savepoint_name
    (null)
    */
    if (input->left_ != NULL) {
      res.push_back(new IR(kOptToSavepoint, string("")));
      if (input->op_->prefix_ != "TO") {
        auto copy = deep_copy(input);
        copy->op_->prefix_ = "TO";
        res.push_back(copy);
      }
      if (input->op_->prefix_ != "TO SAVEPOINT") {
        auto copy = deep_copy(input);
        copy->op_->prefix_ = "TO SAVEPOINT";
        res.push_back(copy);
      }
    } else {
      auto new_ir = get_from_libary_2D_type(kSavepointName);
      if (new_ir) {
        auto copy = new IR(kOptToSavepoint, OP1("TO"), deep_copy(new_ir));
        res.push_back(copy);
        copy = new IR(kOptToSavepoint, OP1("TO SAVEPOINT"), deep_copy(new_ir));
        res.push_back(copy);
      }
    }
    break;
  }
  case kVacuumStatement: {
    /*
    VACUUM opt_schema_name INTO file_path
    VACUUM opt_schema_name
    */
    if (input->right_) {
      auto copy = deep_copy(input);
      deep_delete(copy->right_);
      copy->right_ = NULL;
      copy->op_->middle_ = "";
      copy->operand_num_ = 1;
      res.push_back(copy);
    } else {
      auto new_ir = get_from_libary_2D_type(kFilePath);
      if (new_ir) {
        auto copy = deep_copy(input);
        copy->right_ = deep_copy(new_ir);
        copy->op_->middle_ = "INTO";
        copy->operand_num_ = 2;
        res.push_back(copy);
      }
    }
    break;
  }
  case kOptSchemaName: {
    /*
    schema_name
    (null)
    */
    if (input->left_)
      res.push_back(new IR(kOptSchemaName, string("")));
    else {
      auto new_ir = get_from_libary_2D_type(kSchemaName);
      if (new_ir) {
        auto copy = new IR(kOptSchemaName, OP0(), deep_copy(new_ir));
        res.push_back(copy);
      }
    }
    break;
  }
  case kBeginStatement: {
    /*
    BEGIN opt_transaction
    BEGIN DEFFERED opt_transaction
    BEGIN IMEDIATE opt_transaction
    BEGIN EXCLUSIVE opt_transaction
    */
    if (input->op_->prefix_ != "BEGIN") {
      auto copy = deep_copy(input);
      copy->op_->prefix_ = "BEGIN";
      res.push_back(copy);
    }
    if (input->op_->prefix_ != "BEGIN DEFFERED") {
      auto copy = deep_copy(input);
      copy->op_->prefix_ = "BEGIN DEFFERED";
      res.push_back(copy);
    }
    if (input->op_->prefix_ != "BEGIN IMEDIATE") {
      auto copy = deep_copy(input);
      copy->op_->prefix_ = "BEGIN IMEDIATE";
      res.push_back(copy);
    }
    if (input->op_->prefix_ != "BEGIN EXCLUSIVE") {
      auto copy = deep_copy(input);
      copy->op_->prefix_ = "BEGIN EXCLUSIVE";
      res.push_back(copy);
    }
    break;
  }
  case kCommitStatement: {
    /*
    COMMIT opt_transaction
    END opt_transaction
    */
    if (input->op_->prefix_ != "COMMIT") {
      auto copy = deep_copy(input);
      copy->op_->prefix_ = "COMMIT";
      res.push_back(copy);
    }
    if (input->op_->prefix_ != "END") {
      auto copy = deep_copy(input);
      copy->op_->prefix_ = "END";
      res.push_back(copy);
    }
    break;
  }
  case kOptUpsertClause: {
    /*
    upsert_clause
    (null)
    */
    if (input->left_)
      res.push_back(new IR(kOptUpsertClause, string("")));
    else {
      auto new_ir = get_from_libary_2D_type(kUpsertClause);
      if (new_ir) {
        auto copy = new IR(kOptUpsertClause, OP0(), deep_copy(new_ir));
        res.push_back(copy);
      }
    }
    break;
  }
  case kUpsertClause: {
    /*
    ON CONFLICT DO NOTHING
    ON CONFLICT DO UPDATE SET assign_list opt_where
    ON CONFLICT '(' indexed_column_list ')' opt_where DO NOTHING
    ON CONFLICT '(' indexed_column_list ')' opt_where DO UPDATE SET assign_list opt_where
    */
    if (input->op_->prefix_ != "ON CONFLICT DO NOTHING") {
      res.push_back(new IR(kUpsertClause, OPSTART("ON CONFLICT DO NOTHING")));
    }
    if (input->op_->prefix_ != "ON CONFLICT DO UPDATE SET") {
      auto opt_where = input->right_ ? input->right_ : get_from_libary_2D_type(kOptWhere);
      auto assign_list = (input->left_ && input->left_->type_ == kUnknown) ? input->left_->right_ : get_from_libary_2D_type(kAssignList);
      if (opt_where && assign_list) {
        auto copy = new IR(kUpsertClause, OP1("ON CONFLICT DO UPDATE SET"), deep_copy(assign_list), deep_copy(opt_where));
        res.push_back(copy);
      }
    }
    if (input->op_->prefix_ != "ON CONFLICT (") {
      auto indexed_column_list = (input->left_ && input->left_->type_ == kUnknown) ? input->left_->left_->left_ : get_from_libary_2D_type(kIndexedColumnList);
      auto opt_where = input->right_ ? input->right_ : get_from_libary_2D_type(kOptWhere);
      if (indexed_column_list && opt_where) {
        auto copy = new IR(kUpsertClause, OP3("ON CONFLICT (", ")", "DO NOTHING"), deep_copy(indexed_column_list), deep_copy(opt_where));
        res.push_back(copy);
      }
    }
    if (input->left_ == NULL || input->left_->type_ != kUnknown) {
      IR *indexed_column_list, *opt_where1, *assign_list, *opt_where2;
      if (input->left_ == NULL) {
        indexed_column_list = get_from_libary_2D_type(kIndexedColumnList);
        opt_where1 = get_from_libary_2D_type(kOptWhere);
        assign_list = get_from_libary_2D_type(kAssignList);
        opt_where2 = get_from_libary_2D_type(kOptWhere);
      }
      else if (input->left_->type_ == kAssignList) {
        indexed_column_list = get_from_libary_2D_type(kIndexedColumnList);
        opt_where1 = get_from_libary_2D_type(kOptWhere);
        assign_list = input->left_;
        opt_where2 = input->right_;
      } else {
        indexed_column_list = input->left_;
        opt_where1 = input->right_;
        assign_list = get_from_libary_2D_type(kAssignList);
        opt_where2 = get_from_libary_2D_type(kOptWhere);
      }
      if (indexed_column_list && opt_where1 && assign_list) {
        auto tmp = new IR(kUnknown, OP3("ON CONFLICT (", ")", "DO UPDATE SET"), deep_copy(indexed_column_list), deep_copy(opt_where1));
        tmp = new IR(kUnknown, OP0(), tmp, deep_copy(assign_list));
        auto copy = new IR(kUpsertClause, OP0(), tmp, deep_copy(opt_where2));
        res.push_back(copy);
      }
    }
    break;
  }
  case kOptCollate: {
    /*
    COLLATE collation_name
    (null)
    */
    if (input->left_)
      res.push_back(new IR(kOptCollate, string("")));
    else {
      auto new_ir = get_from_libary_2D_type(kCollationName);
      if (new_ir) {
        auto copy = new IR(kOptCollate, OP1("COLLATE"), deep_copy(new_ir));
        res.push_back(copy);
      }
    }
    break;
  }
  case kOptNull: {
    /*
    NULLS FIRST
    NULLS LAST
    (null)
    */
    if (input->str_val_ != "NULLS FIRST") {
      auto copy = deep_copy(input);
      copy->str_val_ = "NULLS FIRST";
      res.push_back(copy);
    }
    if (input->str_val_ != "NULLS LAST") {
      auto copy = deep_copy(input);
      copy->str_val_ = "NULLS LAST";
      res.push_back(copy);
    }
    if (input->str_val_ != "") {
      auto copy = deep_copy(input);
      copy->str_val_ = "";
      res.push_back(copy);
    }
    break;
  }
  case kOptionalHints: {
    /*
    WITH HINT '(' hint_list ')'
    (null)
    */
    if (input->left_)
      res.push_back(new IR(kOptionalHints, string("")));
    else {
      auto new_ir = get_from_libary_2D_type(kHintList);
      if (new_ir) {
        auto copy = new IR(kOptionalHints, OP3("WITH HINT", "(", ")"), NULL, deep_copy(new_ir));
        res.push_back(copy);
      }
    }
    break;
  }
  case kHint: {
    /*
    IDENTIFIER
    IDENTIFIER '(' literal_list ')'
    */
    if (input->right_) {
      auto copy = deep_copy(input);
      deep_delete(copy->right_);
      copy->right_ = NULL;
      copy->op_->middle_ = "";
      copy->op_->suffix_ = "";
      res.push_back(copy);
    } else {
      auto new_ir = get_from_libary_2D_type(kLiteralList);
      if (new_ir) {
        auto copy = deep_copy(input);
        copy->right_ = deep_copy(new_ir);
        copy->op_->middle_ = "(";
        copy->op_->suffix_ = ")";
        res.push_back(copy);
      }
    }
    break;
  }
  case kExecuteStatement: {
    /*
    EXECUTE IDENTIFIER
    EXECUTE IDENTIFIER '(' opt_literal_list ')'
    */
    if (input->right_) {
      auto copy = deep_copy(input);
      deep_delete(copy->right_);
      copy->right_ = NULL;
      copy->op_->middle_ = "";
      copy->op_->suffix_ = "";
      res.push_back(copy);
    } else {
      auto new_ir = get_from_libary_2D_type(kOptLiteralList);
      if (new_ir) {
        auto copy = deep_copy(input);
        copy->right_ = deep_copy(new_ir);
        copy->op_->middle_ = "(";
        copy->op_->suffix_ = ")";
        res.push_back(copy);
      }
    }
    break;
  }
  case kShowStatement: {
    /*
    SHOW TABLES
    SHOW COLUMNS table_name
    DESCRIBE table_name
    */
    if (input->left_ != NULL) {
      auto copy = deep_copy(input);
      deep_delete(copy->left_);
      copy->left_ = NULL;
      copy->op_->prefix_ = "SHOW TABLES";
      copy->operand_num_ = 0;
      res.push_back(copy);
    }
    if (input->op_->prefix_ != "SHOW COLUMNS") {
      if (input->left_ == NULL) {
        auto new_ir = get_from_libary_2D_type(kTableName);
        if (new_ir) {
          auto copy = deep_copy(input);
          copy->left_ = deep_copy(new_ir);
          copy->op_->prefix_ = "SHOW COLUMNS";
          copy->operand_num_ = 1;
          if (copy->left_->right_ == NULL) {
            copy->left_->left_->id_type_ = id_top_table_name;
          } else {
            copy->left_->right_->id_type_ = id_top_table_name;
          }
          res.push_back(copy);
        }
      } else {
        auto copy = deep_copy(input);
        copy->op_->prefix_ = "SHOW COLUMNS";
        res.push_back(copy);
      }
    }
    if (input->op_->prefix_ != "DESCRIBE") {
      if (input->left_ == NULL) {
        auto new_ir = get_from_libary_2D_type(kTableName);
        if (new_ir) {
          auto copy = deep_copy(input);
          copy->left_ = deep_copy(new_ir);
          copy->op_->prefix_ = "DESCRIBE";
          copy->operand_num_ = 1;
          if (copy->left_->right_ == NULL) {
            copy->left_->left_->id_type_ = id_top_table_name;
          } else {
            copy->left_->right_->id_type_ = id_top_table_name;
          }
          res.push_back(copy);
        }
      } else {
        auto copy = deep_copy(input);
        copy->op_->prefix_ = "DESCRIBE";
        res.push_back(copy);
      }
    }
    break;
  }
  case kAlterStatement: {
    /*
    ALTER TABLE table_name RENAME TO table_name
    ALTER TABLE table_name RENAME opt_column column_name TO column_name
    ALTER TABLE table_name ADD opt_column column_def
    */
    if (input->op_->middle_ != "RENAME TO") {
      if (input->op_->middle_ == "TO") {
        auto new_ir = get_from_libary_2D_type(kTableName);
        if (new_ir) {
          auto copy = deep_copy(input->left_->left_);
          deep_delete(copy->right_);
          copy->right_ = deep_copy(new_ir);
          copy->type_ = kAlterStatement;
          copy->op_->middle_ = "RENAME TO";
          res.push_back(copy);
        }
      }
      if (input->op_->middle_ == "") {
        auto new_ir = get_from_libary_2D_type(kTableName);
        if (new_ir) {
          auto copy = deep_copy(input->left_);
          deep_delete(copy->right_);
          copy->right_ = deep_copy(new_ir);
          copy->type_ = kAlterStatement;
          copy->op_->middle_ = "RENAME TO";
          res.push_back(copy);
        }
      }
    }
    if (input->op_->middle_ != "TO") {
      IR *table_name = NULL, *opt_column = NULL, *column_name1 = NULL, *column_name2 = NULL;
      if (input->left_->type_ != kUnknown) {
        table_name = input->left_;
        opt_column = get_from_libary_2D_type(kOptColumn);
      } else {
        table_name = input->left_->left_;
        opt_column = input->left_->right_;
      }
      column_name1 = get_from_libary_2D_type(kColumnName);
      column_name2 = get_from_libary_2D_type(kColumnName);
      if (opt_column && column_name1) {
        auto tmp = new IR(kUnknown, OP2("ALTER TABLE", "RENAME"), deep_copy(table_name), deep_copy(opt_column));
        tmp = new IR(kUnknown, OP0(), tmp, deep_copy(column_name1));
        tmp = new IR(kAlterStatement, OPMID("TO"), tmp, deep_copy(column_name2));
        res.push_back(tmp);
      }
    }
    if (input->op_->middle_ != "") {
      IR *table_name = NULL, *opt_column = NULL, *column_def = NULL;
      if (input->left_->type_ != kUnknown) {
        table_name = input->left_;
        opt_column = get_from_libary_2D_type(kOptColumn);
      } else {
        table_name = input->left_->left_->left_;
        opt_column = input->left_->left_->right_;
      }
      column_def = get_from_libary_2D_type(kColumnDef);
      if (opt_column && column_def) {
        auto tmp = new IR(kUnknown, OP2("ALTER TABLE", "ADD"), deep_copy(table_name), deep_copy(opt_column));
        tmp = new IR(kAlterStatement, OP0(), tmp, deep_copy(column_def));
        res.push_back(tmp);
      }
    }
    break;
  }
  case kOptColumn: {
    /*
    COLUMN
    (null)
    */
    if (input->str_val_ != "COLUMN") {
      auto copy = deep_copy(input);
      copy->str_val_ = "COLUMN";
      res.push_back(copy);
    }
    if (input->str_val_ != "") {
      auto copy = deep_copy(input);
      copy->str_val_ = "";
      res.push_back(copy);
    }
    break;
  }
  case kCreateStatement: {
    /*
    CREATE TABLE opt_not_exists table_name FROM TBL FILE file_path
    CREATE TABLE opt_not_exists table_name '(' column_def_commalist ')'
    CREATE TABLE opt_not_exists table_name AS select_statement
    CREATE VIEW opt_not_exists table_name opt_column_list AS select_statement
    CREATE opt_unique INDEX opt_not_exists index_name ON table_name '(' ident_commalist ')' opt_where
    CREATE VIRTUAL TABLE opt_not_exists table_name USING module_name
    CREATE VIRTUAL TABLE opt_not_exists table_name USING module_name '(' column_def_commalist ')'
    CREATE trigger_declare BEGIN trigger_cmd_list END
    */
    if (input->op_->prefix_ != "CREATE TABLE" || input->op_->middle_ != "FROM TBL FILE") {
      auto opt_not_exists = get_from_libary_2D_type(kOptNotExists);
      auto table_name = get_from_libary_2D_type(kTableName);
      auto file_path = get_from_libary_2D_type(kFilePath);
      if (opt_not_exists && table_name && file_path) {
        auto table_name_copy = deep_copy(table_name);
        if (table_name_copy->right_ == NULL) {
          table_name_copy->left_->id_type_ = id_create_table_name;
        } else {
          table_name_copy->right_->id_type_ = id_create_table_name;
        }
        auto tmp = new IR(kUnknown, OP0(), deep_copy(opt_not_exists), table_name_copy);
        tmp = new IR(kCreateStatement, OP2("CREATE TABLE", "FROM TBL FILE"), tmp, deep_copy(file_path));
        res.push_back(tmp);
      }
    }
    if (input->op_->prefix_ != "CREATE TABLE" || input->op_->middle_ != "(") {
      auto opt_not_exists = get_from_libary_2D_type(kOptNotExists);
      auto table_name = get_from_libary_2D_type(kTableName);
      auto column_def_comma_list = get_from_libary_2D_type(kColumnDefCommaList);
      if (opt_not_exists && table_name && column_def_comma_list) {
        auto table_name_copy = deep_copy(table_name);
        if (table_name_copy->right_ == NULL) {
          table_name_copy->left_->id_type_ = id_create_table_name;
        } else {
          table_name_copy->right_->id_type_ = id_create_table_name;
        }
        auto tmp = new IR(kUnknown, OP0(), deep_copy(opt_not_exists), table_name_copy);
        tmp = new IR(kCreateStatement, OP3("CREATE TABLE", "(", ")"), tmp, deep_copy(column_def_comma_list));
        res.push_back(tmp);
      }
    }
    if (input->op_->prefix_ != "CREATE TABLE" || input->op_->middle_ != "AS") {
      auto opt_not_exists = get_from_libary_2D_type(kOptNotExists);
      auto table_name = get_from_libary_2D_type(kTableName);
      auto select_statement = get_from_libary_2D_type(kSelectStatement);
      if (opt_not_exists && table_name && select_statement) {
        auto table_name_copy = deep_copy(table_name);
        if (table_name_copy->right_ == NULL) {
          table_name_copy->left_->id_type_ = id_create_table_name;
        } else {
          table_name_copy->right_->id_type_ = id_create_table_name;
        }
        auto tmp = new IR(kUnknown, OP0(), deep_copy(opt_not_exists), table_name_copy);
        tmp = new IR(kCreateStatement, OP2("CREATE TABLE", "AS"), tmp, deep_copy(select_statement));
        res.push_back(tmp);
      }
    }
    if (input->op_->prefix_ != "CREATE VIEW" || input->op_->middle_ != "AS") {
      auto opt_not_exists = get_from_libary_2D_type(kOptNotExists);
      auto table_name = get_from_libary_2D_type(kTableName);
      auto opt_column_list = get_from_libary_2D_type(kOptColumnList);
      auto select_statement = get_from_libary_2D_type(kSelectStatement);
      if (opt_not_exists && table_name && opt_column_list && select_statement) {
        auto table_name_copy = deep_copy(table_name);
        if (table_name_copy->right_ == NULL) {
          table_name_copy->left_->id_type_ = id_create_table_name;
        } else {
          table_name_copy->right_->id_type_ = id_create_table_name;
        }
        auto opt_column_list_copy = deep_copy(opt_column_list);
        if (opt_column_list_copy->left_ != NULL) {
          auto ident_comma_list = opt_column_list_copy->left_;
          auto p = ident_comma_list;
          while (p->right_ != NULL) {
            p->right_->id_type_ = id_create_column_name;
            p = p->left_;
          }
          p->left_->id_type_ = id_create_column_name;
        }
        auto tmp = new IR(kUnknown, OP0(), deep_copy(opt_not_exists), table_name_copy);
        tmp = new IR(kUnknown, OP0(), tmp, opt_column_list_copy);
        tmp = new IR(kCreateStatement, OP2("CREATE VIEW", "AS"), tmp, deep_copy(select_statement));
        res.push_back(tmp);
      }
    }
    if (input->op_->prefix_ != "" || input->op_->middle_ != "") {
      auto opt_unique = get_from_libary_2D_type(kOptUnique);
      auto opt_not_exists = get_from_libary_2D_type(kOptNotExists);
      auto index_name = get_from_libary_2D_type(kIndexName);
      auto table_name = get_from_libary_2D_type(kTableName);
      auto ident_commalist = get_from_libary_2D_type(kIdentCommaList);
      auto opt_where = get_from_libary_2D_type(kOptWhere);
      if (opt_unique && opt_not_exists && index_name && table_name && ident_commalist && opt_where) {
        auto table_name_copy = deep_copy(table_name);
        if (table_name_copy->right_ == NULL) {
          table_name_copy->left_->id_type_ = id_top_table_name;
        } else {
          table_name_copy->right_->id_type_ = id_top_table_name;
        }
        auto ident_commalist_copy = deep_copy(ident_commalist);
        {
          auto p = ident_commalist_copy;
          while (p->right_ != NULL) {
            p->right_->id_type_ = id_column_name;
            p = p->left_;
          }
          p->left_->id_type_ = id_column_name;
        }
        auto tmp = new IR(kUnknown, OP2("CREATE", "INDEX"), deep_copy(opt_unique), deep_copy(opt_not_exists));
        tmp = new IR(kUnknown, OP0(), tmp, deep_copy(index_name));
        tmp = new IR(kUnknown, OPMID("ON"), tmp, table_name_copy);
        tmp = new IR(kUnknown, OP3("", "(", ")"), tmp, ident_commalist_copy);
        tmp = new IR(kCreateStatement, OP0(), tmp, deep_copy(opt_where));
        res.push_back(tmp);
      }
    }
    if (input->op_->prefix_ != "" || input->op_->middle_ != "USING") {
      auto opt_not_exists = get_from_libary_2D_type(kOptNotExists);
      auto table_name = get_from_libary_2D_type(kTableName);
      auto module_name = get_from_libary_2D_type(kModuleName);
      if (opt_not_exists && table_name && module_name) {
        auto table_name_copy = deep_copy(table_name);
        if (table_name_copy->right_ == NULL) {
          table_name_copy->left_->id_type_ = id_create_table_name;
        } else {
          table_name_copy->right_->id_type_ = id_create_table_name;
        }
        auto tmp = new IR(kUnknown, OP1("CREATE VIRTUAL TABLE"), deep_copy(opt_not_exists), table_name_copy);
        tmp = new IR(kCreateStatement, OPMID("USING"), tmp, deep_copy(module_name));
        res.push_back(tmp);
      }
    }
    if (input->op_->prefix_ != "" || input->op_->middle_ != "(") {
      auto opt_not_exists = get_from_libary_2D_type(kOptNotExists);
      auto table_name = get_from_libary_2D_type(kTableName);
      auto module_name = get_from_libary_2D_type(kModuleName);
      auto column_def_comma_list = get_from_libary_2D_type(kColumnDefCommaList);
      if (opt_not_exists && table_name && module_name && column_def_comma_list) {
        auto table_name_copy = deep_copy(table_name);
        if (table_name_copy->right_ == NULL) {
          table_name_copy->left_->id_type_ = id_create_table_name;
        } else {
          table_name_copy->right_->id_type_ = id_create_table_name;
        }
        auto tmp = new IR(kUnknown, OP1("CREATE VIRTUAL TABLE"), deep_copy(opt_not_exists), table_name_copy);
        tmp = new IR(kCreateStatement, OPMID("USING"), tmp, deep_copy(module_name));
        tmp = new IR(kCreateStatement, OP3("", "(", ")"), tmp, deep_copy(column_def_comma_list));
        res.push_back(tmp);
      }
    }
    if (input->op_->prefix_ != "CREATE" || input->op_->middle_ != "BEGIN") {
      auto trigger_declare = get_from_libary_2D_type(kTriggerDeclare);
      auto trigger_cmd_list = get_from_libary_2D_type(kTriggerCmdList);
      if (trigger_declare && trigger_cmd_list) {
        auto tmp = new IR(kCreateStatement, OP3("CREATE", "BEGIN", "END"), deep_copy(trigger_declare), deep_copy(trigger_cmd_list));
        res.push_back(tmp);
      }
    }
    break;
  }
  case kOptUnique: {
    /*
    UNIQUE
    (null)
    */
    if (input->str_val_ != "UNIQUE") {
      auto copy = deep_copy(input);
      copy->str_val_ = "UNIQUE";
      res.push_back(copy);
    }
    if (input->str_val_ != "") {
      auto copy = deep_copy(input);
      copy->str_val_ = "";
      res.push_back(copy);
    }
    break;
  }
  case kOptTmp: {
    /*
    TEMP
    (null)
    */
    if (input->str_val_ != "TEMP") {
      auto copy = deep_copy(input);
      copy->str_val_ = "TEMP";
      res.push_back(copy);
    }
    if (input->str_val_ != "") {
      auto copy = deep_copy(input);
      copy->str_val_ = "";
      res.push_back(copy);
    }
    break;
  }
  case kOptTriggerTime: {
    /*
    BEFORE
    AFTER
    INSTEAD OF
    (null)
    */
    if (input->str_val_ != "BEFORE") {
      auto copy = deep_copy(input);
      copy->str_val_ = "BEFORE";
      res.push_back(copy);
    }
    if (input->str_val_ != "AFTER") {
      auto copy = deep_copy(input);
      copy->str_val_ = "AFTER";
      res.push_back(copy);
    }
    if (input->str_val_ != "INSTEAD OF") {
      auto copy = deep_copy(input);
      copy->str_val_ = "INSTEAD OF";
      res.push_back(copy);
    }
    if (input->str_val_ != "") {
      auto copy = deep_copy(input);
      copy->str_val_ = "";
      res.push_back(copy);
    }
    break;
  }
  case kTriggerEvent: {
    /*
    DELETE
    INSERT
    UPDATE opt_of_column_list
    */
    if (input->op_ != NULL || input->str_val_ != "DELETE") {
      auto tmp = new IR(kTriggerEvent, string("DELETE"));
      res.push_back(tmp);
    }
    if (input->op_ != NULL || input->str_val_ != "INSERT") {
      auto tmp = new IR(kTriggerEvent, string("INSERT"));
      res.push_back(tmp);
    }
    if (input->op_ == NULL) {
      auto new_ir = get_from_libary_2D_type(kOptOfColumnList);
      if (new_ir) {
        auto tmp = new IR(kTriggerEvent, OP1("UPDATE"), deep_copy(new_ir));
        res.push_back(tmp);
      }
    }
    break;
  }
  case kOptOfColumnList: {
    /*
    OF ident_commalist
    (null)
    */
    if (input->left_)
      res.push_back(new IR(kOptOfColumnList, string("")));
    else {
      auto new_ir = get_from_libary_2D_type(kIdentCommaList);
      if (new_ir) {
        auto copy = new IR(kOptOfColumnList, OP1("OF"), deep_copy(new_ir));
        res.push_back(copy);
      }
    }
    break;
  }
  case kOptForEach: {
    /*
    FOR EACH ROW
    (null)
    */
    if (input->str_val_ != "FOR EACH ROW") {
      auto copy = deep_copy(input);
      copy->str_val_ = "FOR EACH ROW";
      res.push_back(copy);
    }
    if (input->str_val_ != "") {
      auto copy = deep_copy(input);
      copy->str_val_ = "";
      res.push_back(copy);
    }
    break;
  }
  case kOptWhen: {
    /*
    WHEN expr
    (null)
    */
    if (input->left_)
      res.push_back(new IR(kOptWhen, string("")));
    else {
      auto new_ir = get_from_libary_2D_type(candidate_type_expr[get_rand_int(candidate_type_expr.size())]);
      if (new_ir) {
        auto copy = new IR(kOptWhen, OP1("WHEN"), deep_copy(new_ir));
        res.push_back(copy);
      }
    }
    break;
  }
  case kOptNotExists: {
    /*
    IF NOT EXISTS
    (null)
    */
    if (input->str_val_ != "IF NOT EXISTS") {
      auto copy = deep_copy(input);
      copy->str_val_ = "IF NOT EXISTS";
      res.push_back(copy);
    }
    if (input->str_val_ != "") {
      auto copy = deep_copy(input);
      copy->str_val_ = "";
      res.push_back(copy);
    }
    break;
  }
  case kOptColumnArglist: {
    /*
    column_arglist
    (null)
    */
    if (input->left_)
      res.push_back(new IR(kOptColumnArglist, string("")));
    else {
      auto new_ir = get_from_libary_2D_type(kColumnArglist);
      if (new_ir) {
        auto copy = new IR(kOptColumnArglist, OP0(), deep_copy(new_ir));
        res.push_back(copy);
      }
    }
    break;
  }
  case kColumnArg: {
    /*
    NULL opt_on_conflict
    NOT NULL opt_on_conflict
    PRIMARY KEY opt_order_type opt_on_conflict opt_autoinc
    UNIQUE opt_on_conflict
    ----------
    GENERATED ALWAYS AS '(' expr ')'
    AS '(' expr ')'
    CHECK '(' expr ')'
    */
    if ((input->left_->type_ == kOptOnConflict || input->left_->type_ == kUnknown) && input->op_->prefix_ != "NULL") {
      if (input->op_->prefix_ == "") {
        auto opt_on_conflict = input->left_->right_;
        auto tmp = new IR(kColumnArg, OP1("NULL"), deep_copy(opt_on_conflict));
        res.push_back(tmp);
      } else {
      auto copy = deep_copy(input);
      copy->op_->prefix_ = "NULL";
      res.push_back(copy);
      }
    }
    if ((input->left_->type_ == kOptOnConflict || input->left_->type_ == kUnknown) && input->op_->prefix_ != "NOT NULL") {
      if (input->op_->prefix_ == "") {
        auto opt_on_conflict = input->left_->right_;
        auto tmp = new IR(kColumnArg, OP1("NOT NULL"), deep_copy(opt_on_conflict));
        res.push_back(tmp);
      } else {
      auto copy = deep_copy(input);
      copy->op_->prefix_ = "NOT NULL";
      res.push_back(copy);
      }
    }
    if ((input->left_->type_ == kOptOnConflict || input->left_->type_ == kUnknown) && input->op_->prefix_ != "") {
      auto opt_order_type = get_from_libary_2D_type(kOptOrderType);
      auto opt_on_conflict = input->left_;
      auto opt_autoinc = get_from_libary_2D_type(kOptAutoinc);
      if (opt_order_type && opt_autoinc) {
        auto tmp = new IR(kUnknown, OP1("PRIMARY KEY"), deep_copy(opt_order_type), deep_copy(opt_on_conflict));
        tmp = new IR(kColumnArg, OP0(), tmp, deep_copy(opt_autoinc));
        res.push_back(tmp);
      }
    }
    if ((input->left_->type_ == kOptOnConflict || input->left_->type_ == kUnknown) && input->op_->prefix_ != "UNIQUE") {
      if (input->op_->prefix_ == "") {
        auto opt_on_conflict = input->left_->right_;
        auto tmp = new IR(kColumnArg, OP1("UNIQUE"), deep_copy(opt_on_conflict));
        res.push_back(tmp);
      } else {
      auto copy = deep_copy(input);
      copy->op_->prefix_ = "UNIQUE";
      res.push_back(copy);
      }
    }
    if ((input->left_->type_ != kOptOnConflict && input->left_->type_ != kUnknown) && input->op_->prefix_ != "GENERATED ALWAYS AS(") {
      auto copy = deep_copy(input);
      copy->op_->middle_ = "GENERATED ALWAYS AS(";
      res.push_back(copy);
    }
    if ((input->left_->type_ != kOptOnConflict && input->left_->type_ != kUnknown) && input->op_->prefix_ != "AS(") {
      auto copy = deep_copy(input);
      copy->op_->middle_ = "AS(";
      res.push_back(copy);
    }
    if ((input->left_->type_ != kOptOnConflict && input->left_->type_ != kUnknown) && input->op_->prefix_ != "CHECK(") {
      auto copy = deep_copy(input);
      copy->op_->middle_ = "CHECK(";
      res.push_back(copy);
    }
    break;
  }
  case kOptOnConflict: {
    /*
    ON CONFLICT resolve_type
    (null)
    */
    if (input->left_)
      res.push_back(new IR(kOptOnConflict, string("")));
    else {
      auto new_ir = get_from_libary_2D_type(kResolveType);
      if (new_ir) {
        auto copy = new IR(kOptOnConflict, OP1("ON CONFLICT"), deep_copy(new_ir));
        res.push_back(copy);
      }
    }
    break;
  }
  case kResolveType: {
    /*
    IGNORE
    REPLACE
    ROLLBACK
    ABORT
    FAIL
    */
    if (input->str_val_ != "IGNORE") {
      auto copy = deep_copy(input);
      copy->str_val_ = "IGNORE";
      res.push_back(copy);
    }
    if (input->str_val_ != "REPLACE") {
      auto copy = deep_copy(input);
      copy->str_val_ = "REPLACE";
      res.push_back(copy);
    }
    if (input->str_val_ != "ROLLBACK") {
      auto copy = deep_copy(input);
      copy->str_val_ = "ROLLBACK";
      res.push_back(copy);
    }
    if (input->str_val_ != "ABORT") {
      auto copy = deep_copy(input);
      copy->str_val_ = "ABORT";
      res.push_back(copy);
    }
    if (input->str_val_ != "FAIL") {
      auto copy = deep_copy(input);
      copy->str_val_ = "FAIL";
      res.push_back(copy);
    }
    break;
  }
  case kOptAutoinc: {
    /*
    AUTOINCR
    (null)
    */
    if (input->str_val_ != "AUTOINCR") {
      auto copy = deep_copy(input);
      copy->str_val_ = "AUTOINCR";
      res.push_back(copy);
    }
    if (input->str_val_ != "") {
      auto copy = deep_copy(input);
      copy->str_val_ = "";
      res.push_back(copy);
    }
    break;
  }
  case kColumnType: {
    /*
    INT
    INTEGER
    LONG
    FLOAT
    DOUBLE
    VARCHAR '(' INTVAL ')'
    CHAR '(' INTVAL ')'
    TEXT
    (null)
    */
    if (input->str_val_ != "INT") {
      auto copy = deep_copy(input);
      copy->str_val_ = "INT";
      res.push_back(copy);
    }
    if (input->str_val_ != "INTEGER") {
      auto copy = deep_copy(input);
      copy->str_val_ = "INTEGER";
      res.push_back(copy);
    }
    if (input->str_val_ != "LONG") {
      auto copy = deep_copy(input);
      copy->str_val_ = "LONG";
      res.push_back(copy);
    }
    if (input->str_val_ != "FLOAT") {
      auto copy = deep_copy(input);
      copy->str_val_ = "FLOAT";
      res.push_back(copy);
    }
    if (input->str_val_ != "DOUBLE") {
      auto copy = deep_copy(input);
      copy->str_val_ = "DOUBLE";
      res.push_back(copy);
    }
    if (input->str_val_.rfind("VARCHAR(", 0) != 0) {
      auto copy = deep_copy(input);
      copy->str_val_ = "VARCHAR(" + std::to_string(get_a_val()) + ")";
      res.push_back(copy);
    }
    if (input->str_val_.rfind("CHAR(", 0) != 0) {
      auto copy = deep_copy(input);
      copy->str_val_ = "CHAR(" + std::to_string(get_a_val()) + ")";
      res.push_back(copy);
    }
    if (input->str_val_ != "TEXT") {
      auto copy = deep_copy(input);
      copy->str_val_ = "TEXT";
      res.push_back(copy);
    }
    if (input->str_val_ != "") {
      auto copy = deep_copy(input);
      copy->str_val_ = "";
      res.push_back(copy);
    }
    break;
  }
  case kDropStatement: {
    /*
    DROP TABLE opt_exists table_name
    DROP VIEW opt_exists table_name
    DEALLOCATE PREPARE IDENTIFIER
    DROP TRIGGER opt_exists schema_name '.' trigger_name
    DROP TRIGGER opt_exists trigger_name
    */
    if (input->op_->prefix_ == "DEALLOCATE PREPARE")
      break;
    if (input->op_->prefix_ == "DROP TABLE") {
      auto copy = deep_copy(input);
      copy->op_->prefix_ = "DROP VIEW";
      res.push_back(copy);
    }
    if (input->op_->prefix_ == "DROP VIEW") {
      auto copy = deep_copy(input);
      copy->op_->prefix_ = "DROP TABLE";
      res.push_back(copy);
    }
    if (input->op_->prefix_ == "DROP TRIGGER") {
      if (input->right_->type_ == kUnknown) {
        auto copy = deep_copy(input);
        auto trigger_name_copy = deep_copy(input->right_->right_);
        deep_delete(copy->right_);
        copy->right_ = trigger_name_copy;
        res.push_back(copy);
      } else {
        auto opt_exist = input->left_;
        auto trigger_name = input->right_;
        auto schema_name = get_from_libary_2D_type(kSchemaName);
        if (schema_name) {
          auto tmp = new IR(kUnknown, OPMID("."), deep_copy(schema_name), deep_copy(trigger_name));
          tmp = new IR(kDropStatement, OP1("DROP TRIGGER"), deep_copy(opt_exist), tmp);
          res.push_back(tmp);
        }
      }
    }
    break;
  }
  case kOptExists: {
    /*
    IF EXISTS
    (null)
    */
    if (input->str_val_ != "IF EXISTS") {
      auto copy = deep_copy(input);
      copy->str_val_ = "IF EXISTS";
      res.push_back(copy);
    }
    if (input->str_val_ != "") {
      auto copy = deep_copy(input);
      copy->str_val_ = "";
      res.push_back(copy);
    }
    break;
  }
  case kInsertStatement: {
    /*
    insert_type INTO table_name opt_column_list VALUES super_list opt_upsert_clause
    insert_type INTO table_name opt_column_list select_no_paren opt_upsert_clause
    */
    if (input->left_->op_->middle_ == "VALUES") {
      auto select_no_paren = get_from_libary_2D_type(kSelectNoParen);
      if (select_no_paren) {
        auto copy = deep_copy(input);
        deep_delete(copy->left_->right_);
        copy->left_->right_ = deep_copy(select_no_paren);
        copy->left_->op_->middle_ = "";
        res.push_back(copy);
      }
    } else {
      auto super_list = get_from_libary_2D_type(kSuperList);
      if (super_list) {
        auto copy = deep_copy(input);
        deep_delete(copy->left_->right_);
        copy->left_->right_ = deep_copy(super_list);
        copy->left_->op_->middle_ = "VALUES";
        res.push_back(copy);
      }
    }
    break;
  }
  case kInsertType: {
    /*
    INSERT
    REPLACE
    INSERT OR resolve_type
    */
    if (input->left_) {
      res.push_back(new IR(kInsertType, string("INSERT")));
      res.push_back(new IR(kInsertType, string("REPLACE")));
    } else {
      auto new_ir = get_from_libary_2D_type(kResolveType);
      if (new_ir) {
        auto copy = new IR(kInsertType, OP1("INSERT OR"), deep_copy(new_ir));
        res.push_back(copy);
      }
      if (input->str_val_ == "INSERT")
        res.push_back(new IR(kInsertType, string("REPLACE")));
      else
        res.push_back(new IR(kInsertType, string("INSERT")));
    }
    break;
  }
  case kOptColumnList: {
    /*
    '(' ident_commalist ')'
    (null)
    */
    if (input->left_)
      res.push_back(new IR(kOptColumnList, string("")));
    else {
      auto new_ir = get_from_libary_2D_type(kIdentCommaList);
      if (new_ir) {
        auto copy = new IR(kOptColumnList, OP3("(", "", ")"), deep_copy(new_ir));
        res.push_back(copy);
      }
    }
    break;
  }
  case kSelectStatement: {
    /*
    opt_with_clause select_with_paren
    opt_with_clause select_no_paren
    opt_with_clause select_with_paren set_operator select_paren_or_clause opt_order opt_limit
    */
    if (input->right_->type_ != kSelectWithParen) {
      if (input->right_->type_ == kSelectNoParen) {
        auto select_with_paren = get_from_libary_2D_type(kSelectWithParen);
        if (select_with_paren) {
          auto copy = deep_copy(input);
          deep_delete(copy->right_);
          copy->right_ = deep_copy(select_with_paren);
          res.push_back(copy);
        }
      } else {
        auto p = input;
        while (p->right_->type_ != kSelectWithParen) p = p->left_;
        auto copy = deep_copy(p);
        copy->type_ = kSelectStatement;
        res.push_back(copy);
      }
    }
    if (input->right_->type_ != kSelectNoParen) {
      if (input->right_->type_ == kSelectWithParen) {
        auto select_no_paren = get_from_libary_2D_type(kSelectNoParen);
        if (select_no_paren) {
          auto copy = deep_copy(input);
          deep_delete(copy->right_);
          copy->right_ = deep_copy(select_no_paren);
          res.push_back(copy);
        }
      } else {
        auto p = input;
        while (p->right_->type_ != kSelectWithParen) p = p->left_;
        auto opt_with_clause = p->left_;
        auto select_no_paren = get_from_libary_2D_type(kSelectNoParen);
        if (select_no_paren) {
          auto tmp = new IR(kSelectStatement, OP0(), deep_copy(opt_with_clause), deep_copy(select_no_paren));
          res.push_back(tmp);
        }
      }
    }
    if (input->left_->type_ != kUnknown) {
      IR *select_with_paren;
      auto opt_with_clause = input->left_;
      if (input->right_->type_ == kSelectWithParen)
        select_with_paren = input->right_;
      else
        select_with_paren = get_from_libary_2D_type(kSelectWithParen);
      auto set_operator = get_from_libary_2D_type(kSetOperator);
      auto select_paren_or_clause = get_from_libary_2D_type(kSelectParenOrClause);
      auto opt_order = get_from_libary_2D_type(kOptOrder);
      auto opt_limit = get_from_libary_2D_type(kOptLimit);
      if (select_with_paren && set_operator && select_paren_or_clause && opt_order) {
        auto tmp = new IR(kUnknown, OP0(), deep_copy(opt_with_clause), deep_copy(select_with_paren));
        tmp = new IR(kUnknown, OP0(), tmp, deep_copy(set_operator));
        tmp = new IR(kUnknown, OP0(), tmp, deep_copy(select_paren_or_clause));
        if (opt_limit) {
          tmp = new IR(kUnknown, OP0(), tmp, deep_copy(opt_order));
          tmp = new IR(kSelectStatement, OP0(), tmp, deep_copy(opt_limit));
        } else {
          tmp = new IR(kSelectStatement, OP0(), tmp, deep_copy(opt_order));
        }
        res.push_back(tmp);
      }
    }
    break;
  }
  case kSelectWithParen: {
    /*
    '(' select_no_paren ')'
    '(' select_with_paren ')'
    */
    if (input->left_->type_ != kSelectNoParen) {
      auto select_no_paren = get_from_libary_2D_type(kSelectNoParen);
      if (select_no_paren) {
        auto copy = deep_copy(input);
        deep_delete(copy->left_);
        copy->left_ = deep_copy(select_no_paren);
        res.push_back(copy);
      }
    }
    if (input->left_->type_ != kSelectWithParen) {
      auto select_with_paren = get_from_libary_2D_type(kSelectWithParen);
      if (select_with_paren) {
        auto copy = deep_copy(input);
        deep_delete(copy->left_);
        copy->left_ = deep_copy(select_with_paren);
        res.push_back(copy);
      }
    }
    break;
  }
  case kSelectParenOrClause: {
    /*
    select_with_paren
    select_clause
    */
    if (input->left_->type_ != kSelectWithParen) {
      auto select_with_paren = get_from_libary_2D_type(kSelectWithParen);
      if (select_with_paren) {
        auto copy = deep_copy(input);
        deep_delete(copy->left_);
        copy->left_ = deep_copy(select_with_paren);
        res.push_back(copy);
      }
    }
    if (input->left_->type_ != kSelectClause) {
      auto select_clause = get_from_libary_2D_type(kSelectClause);
      if (select_clause) {
        auto copy = deep_copy(input);
        deep_delete(copy->left_);
        copy->left_ = deep_copy(select_clause);
        res.push_back(copy);
      }
    }
    break;
  }
  case kSelectNoParen: {
    /*
    select_clause opt_order opt_limit
    select_clause set_operator select_paren_or_clause opt_order opt_limit
    */
    if (input->right_->type_ == kOptLimit) {
      if (input->left_->left_->type_ != kSelectClause) {
        auto select_clause = input->left_->left_->left_->left_;
        auto opt_order = input->left_->right_;
        auto opt_limit = input->right_;
        auto tmp = new IR(kUnknown, OP0(), deep_copy(select_clause), deep_copy(opt_order));
        tmp = new IR(kSelectNoParen, OP0(), tmp, deep_copy(opt_limit));
        res.push_back(tmp);
      } else {
        auto select_clause = input->left_->left_;
        auto set_operator = get_from_libary_2D_type(kSetOperator);
        auto select_paren_or_clause = get_from_libary_2D_type(kSelectParenOrClause);
        auto opt_order = input->left_->right_;
        auto opt_limit = input->right_;
        if (set_operator && select_paren_or_clause) {
          auto tmp = new IR(kUnknown, OP0(), deep_copy(select_clause), deep_copy(set_operator));
          tmp = new IR(kUnknown, OP0(), tmp, deep_copy(select_paren_or_clause));
          tmp = new IR(kUnknown, OP0(), tmp, deep_copy(opt_order));
          tmp = new IR(kSelectNoParen, OP0(), tmp, deep_copy(opt_limit));
          res.push_back(tmp);
        }
      }
    } else {
      if (input->left_->type_ != kSelectClause) {
        auto select_clause = input->left_->left_->left_;
        auto opt_order = input->right_;
        auto tmp = new IR(kSelectNoParen, OP0(), deep_copy(select_clause), deep_copy(opt_order));
        res.push_back(tmp);
      } else {
        auto select_clause = input->left_;
        auto set_operator = get_from_libary_2D_type(kSetOperator);
        auto select_paren_or_clause = get_from_libary_2D_type(kSelectParenOrClause);
        auto opt_order = input->right_;
        if (set_operator && select_paren_or_clause) {
          auto tmp = new IR(kUnknown, OP0(), deep_copy(select_clause), deep_copy(set_operator));
          tmp = new IR(kUnknown, OP0(), tmp, deep_copy(select_paren_or_clause));
          tmp = new IR(kSelectNoParen, OP0(), tmp, deep_copy(opt_order));
          res.push_back(tmp);
        }
      }
    }
    break;
  }
  case kSetType: {
    /*
    UNION
    INTERSECT
    EXCEPT
    */
    if (input->str_val_ != "UNION") {
      auto copy = deep_copy(input);
      copy->str_val_ = "UNION";
      res.push_back(copy);
    }
    if (input->str_val_ != "INTERSECT") {
      auto copy = deep_copy(input);
      copy->str_val_ = "INTERSECT";
      res.push_back(copy);
    }
    if (input->str_val_ != "EXCEPT") {
      auto copy = deep_copy(input);
      copy->str_val_ = "EXCEPT";
      res.push_back(copy);
    }
    break;
  }
  case kOptAll: {
    /*
    ALL
    (null)
    */
    if (input->str_val_ != "ALL") {
      auto copy = deep_copy(input);
      copy->str_val_ = "ALL";
      res.push_back(copy);
    }
    if (input->str_val_ != "") {
      auto copy = deep_copy(input);
      copy->str_val_ = "";
      res.push_back(copy);
    }
    break;
  }
  case kSelectClause: {
    /*
    SELECT opt_top opt_distinct select_list opt_from_clause opt_where opt_group
    SELECT opt_top opt_distinct select_list opt_from_clause opt_where opt_group window_clause
    */
    if (input->right_->type_ == kOptGroup) {
      auto window_clause = get_from_libary_2D_type(kWindowClause);
      if (window_clause) {
        auto copy = deep_copy(input);
        copy->type_ = kUnknown;
        auto tmp = new IR(kSelectClause, OP0(), copy, deep_copy(window_clause));
        res.push_back(tmp);
      }
    } else {
      auto copy = deep_copy(input->left_);
      copy->type_ = kSelectClause;
      res.push_back(copy);
    }
    break;
  }
  case kWindow: {
    /*
    opt_base_window_name PARTITION BY expr_list opt_order opt_frame
    opt_base_window_name opt_order opt_frame
    */
    if (input->left_->left_->type_ == kUnknown) {
      auto opt_base_window_name = input->left_->left_->left_;
      auto opt_order = input->left_->right_;
      auto opt_frame = input->right_;
      auto tmp = new IR(kUnknown, OP0(), deep_copy(opt_base_window_name), deep_copy(opt_order));
      tmp = new IR(kWindow, OP0(), tmp, deep_copy(opt_frame));
      res.push_back(tmp);
    } else {
      auto opt_base_window_name = input->left_->left_;
      auto expr_list = get_from_libary_2D_type(kExprList);
      auto opt_order = input->left_->right_;
      auto opt_frame = input->right_;
      if (expr_list) {
        auto tmp = new IR(kUnknown, OPMID("PARTITION BY"), deep_copy(opt_base_window_name), deep_copy(expr_list));
        tmp = new IR(kUnknown, OP0(), tmp, deep_copy(opt_order));
        tmp = new IR(kWindow, OP0(), tmp, deep_copy(opt_frame));
        res.push_back(tmp);
      }
    }
    break;
  }
  case kOptBaseWindowName: {
    /*
    IDENTIFIER
    (null)
    */
    if (input->left_)
      res.push_back(new IR(kOptBaseWindowName, string("")));
    else {
      auto new_ir = get_from_libary_2D_type(kIdentifier);
      if (new_ir) {
        auto copy = new IR(kOptBaseWindowName, OP0(), deep_copy(new_ir));
        res.push_back(copy);
      }
    }
    break;
  }
  case kOptFrame: {
    /*
    range_or_rows frame_bound_s opt_frame_exclude
    range_or_rows BETWEEN frame_bound_s AND frame_bound_e opt_frame_exclude
    (null)
    */
    if (input->left_ != NULL) {
      res.push_back(new IR(kOptFrame, string("")));
      if (input->left_->right_->type_ == kFrameBoundS) {
        auto range_or_row = input->left_->left_;
        auto frame_bound_s = input->left_->right_;
        auto frame_bound_e = get_from_libary_2D_type(kFrameBoundE);
        auto opt_frame_exclude = input->right_;
        if (frame_bound_e) {
          auto tmp = new IR(kUnknown, OP2("BEWTEEN", "AND"), deep_copy(frame_bound_s), deep_copy(frame_bound_e));
          tmp = new IR(kUnknown, OP0(), deep_copy(range_or_row), tmp);
          tmp = new IR(kOptFrame, OP0(), tmp, deep_copy(opt_frame_exclude));
          res.push_back(tmp);
        }
      } else {
        auto range_or_row = input->left_->left_;
        auto frame_bound_s = input->left_->right_->left_;
        auto opt_frame_exclude = input->right_;
        auto tmp = new IR(kUnknown, OP0(), deep_copy(range_or_row), deep_copy(frame_bound_s));
        tmp = new IR(kOptFrame, OP0(), tmp, deep_copy(opt_frame_exclude));
        res.push_back(tmp);
      }
    } else {
      auto tmp = get_from_libary_2D_type(kOptFrame);
      if (tmp && tmp->left_ != NULL) res.push_back(deep_copy(tmp));
    }
    break;
  }
  case kRangeOrRows: {
    /*
    RANGE
    ROWS
    GROUPS
    */
    if (input->str_val_ != "RANGE") {
      auto copy = deep_copy(input);
      copy->str_val_ = "RANGE";
      res.push_back(copy);
    }
    if (input->str_val_ != "ROWS") {
      auto copy = deep_copy(input);
      copy->str_val_ = "ROWS";
      res.push_back(copy);
    }
    if (input->str_val_ != "GROUPS") {
      auto copy = deep_copy(input);
      copy->str_val_ = "GROUPS";
      res.push_back(copy);
    }
    break;
  }
  case kFrameBoundS: {
    /*
    frame_bound
    UNBOUNDED PRECEDING
    */
    if (input->left_)
      res.push_back(new IR(kFrameBoundS, string("UNBOUNDED PRECEDING")));
    else {
      auto new_ir = get_from_libary_2D_type(kFrameBound);
      if (new_ir) {
        auto copy = new IR(kFrameBoundS, OP0(), deep_copy(new_ir));
        res.push_back(copy);
      }
    }
    break;
  }
  case kFrameBoundE: {
    /*
    frame_bound
    UNBOUNDED FOLLOWING
    */
    if (input->left_)
      res.push_back(new IR(kFrameBoundE, string("UNBOUNDED FOLLOWING")));
    else {
      auto new_ir = get_from_libary_2D_type(kFrameBound);
      if (new_ir) {
        auto copy = new IR(kFrameBoundE, OP0(), deep_copy(new_ir));
        res.push_back(copy);
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
      res.push_back(new IR(kFrameBound, OP1("CURRENT ROW")));
      if (input->op_->suffix_ != "PRECEDING") {
        auto copy = deep_copy(input);
        copy->op_->suffix_ = "PRECEDING";
        res.push_back(copy);
      }
      if (input->op_->suffix_ != "FOLLOWING") {
        auto copy = deep_copy(input);
        copy->op_->suffix_ = "FOLLOWING";
        res.push_back(copy);
      }
    } else {
      auto expr = get_from_libary_2D_type(candidate_type_expr[get_rand_int(candidate_type_expr.size())]);
      if (expr) {
        res.push_back(new IR(kFrameBound, OPEND("PRECEDING"), deep_copy(expr)));
        res.push_back(new IR(kFrameBound, OPEND("FOLLOWING"), deep_copy(expr)));
      }
    }
    break;
  }
  case kOptFrameExclude: {
    /*
    EXCLUDE frame_exclude
    (null)
    */
    if (input->left_)
      res.push_back(new IR(kOptFrameExclude, string("")));
    else {
      auto new_ir = get_from_libary_2D_type(kFrameExclude);
      if (new_ir) {
        auto copy = new IR(kOptFrameExclude, OP1("EXCLUDE"), deep_copy(new_ir));
        res.push_back(copy);
      }
    }
    break;
  }
  case kFrameExclude: {
    /*
    NO OTHERS
    CURRENT ROW
    GROUP
    TIES
    */
    if (input->str_val_ != "NO OTHERS") {
      auto copy = deep_copy(input);
      copy->str_val_ = "NO OTHERS";
      res.push_back(copy);
    }
    if (input->str_val_ != "CURRENT ROW") {
      auto copy = deep_copy(input);
      copy->str_val_ = "CURRENT ROW";
      res.push_back(copy);
    }
    if (input->str_val_ != "GROUP") {
      auto copy = deep_copy(input);
      copy->str_val_ = "GROUP";
      res.push_back(copy);
    }
    if (input->str_val_ != "TIES") {
      auto copy = deep_copy(input);
      copy->str_val_ = "TIES";
      res.push_back(copy);
    }
    break;
  }
  case kOptDistinct: {
    /*
    DISTINCT
    (null)
    */
    if (input->str_val_ != "DISTINCT") {
      auto copy = deep_copy(input);
      copy->str_val_ = "DISTINCT";
      res.push_back(copy);
    }
    if (input->str_val_ != "") {
      auto copy = deep_copy(input);
      copy->str_val_ = "";
      res.push_back(copy);
    }
    break;
  }
  case kOptFromClause: {
    /*
    from_clause
    (null)
    */
    if (input->left_)
      res.push_back(new IR(kOptFromClause, string("")));
    else {
      auto new_ir = get_from_libary_2D_type(kFromClause);
      if (new_ir) {
        auto copy = new IR(kOptFromClause, OP0(), deep_copy(new_ir));
        res.push_back(copy);
      }
    }
    break;
  }
  case kOptWhere: {
    /*
    WHERE expr
    (null)
    */
    if (input->left_)
      res.push_back(new IR(kOptWhere, string("")));
    else {
      auto new_ir = get_from_libary_2D_type(candidate_type_expr[get_rand_int(candidate_type_expr.size())]);
      if (new_ir) {
        auto copy = new IR(kOptWhere, OPSTART("WHERE"), deep_copy(new_ir));
        res.push_back(copy);
      }
    }
    break;
  }
  case kOptGroup: {
    /*
    GROUP BY expr_list opt_having
    (null)
    */
    if (input->left_)
      res.push_back(new IR(kOptGroup, string("")));
    else {
      auto expr_list = get_from_libary_2D_type(kExprList);
      auto opt_having = get_from_libary_2D_type(kOptHaving);
      if (expr_list && opt_having) {
        auto copy = new IR(kOptGroup, OPSTART("GROUP BY"), deep_copy(expr_list), deep_copy(opt_having));
        res.push_back(copy);
      }
    }
    break;
  }
  case kOptHaving: {
    /*
    HAVING expr
    (null)
    */
    if (input->left_)
      res.push_back(new IR(kOptHaving, string("")));
    else {
      auto new_ir = get_from_libary_2D_type(candidate_type_expr[get_rand_int(candidate_type_expr.size())]);
      if (new_ir) {
        auto copy = new IR(kOptHaving, OP1("HAVING"), deep_copy(new_ir));
        res.push_back(copy);
      }
    }
    break;
  }
  case kOptOrder: {
    /*
    ORDER BY order_list
    (null)
    */
    if (input->left_)
      res.push_back(new IR(kOptOrder, string("")));
    else {
      auto new_ir = get_from_libary_2D_type(kOrderList);
      if (new_ir) {
        auto copy = new IR(kOptOrder, OP1("ORDER BY"), deep_copy(new_ir));
        res.push_back(copy);
      }
    }
    break;
  }
  case kOptOrderType: {
    /*
    ASC
    DESC
    (null)
    */
    if (input->str_val_ != "ASC") {
      auto copy = deep_copy(input);
      copy->str_val_ = "ASC";
      res.push_back(copy);
    }
    if (input->str_val_ != "DESC") {
      auto copy = deep_copy(input);
      copy->str_val_ = "DESC";
      res.push_back(copy);
    }
    if (input->str_val_ != "") {
      auto copy = deep_copy(input);
      copy->str_val_ = "";
      res.push_back(copy);
    }
    break;
  }
  case kOptTop: {
    /*
    TOP int_literal
    (null)
    */
    if (input->left_)
      res.push_back(new IR(kOptTop, string("")));
    else {
      auto new_ir = get_from_libary_2D_type(kIntLiteral);
      if (new_ir) {
        auto copy = new IR(kOptTop, OPSTART("TOP"), deep_copy(new_ir));
        res.push_back(copy);
      }
    }
    break;
  }
  case kOptLimit: {
    /*
    LIMIT expr
    OFFSET expr
    LIMIT expr OFFSET expr
    LIMIT ALL
    LIMIT ALL OFFSET expr
    */
    if (input->op_ == NULL || input->op_->prefix_ != "LIMIT" || input->op_->middle_ != "") {
      auto expr = input->left_ != NULL ? input->left_ : get_from_libary_2D_type(candidate_type_expr[get_rand_int(candidate_type_expr.size())]);
      if (expr) {
        auto tmp = new IR(kOptLimit, OPSTART("LIMIT"), deep_copy(expr));
        res.push_back(tmp);
      }
    }
    if (input->op_ == NULL || input->op_->prefix_ != "OFFSET" || input->op_->middle_ != "") {
      auto expr = input->left_ != NULL ? input->left_ : get_from_libary_2D_type(candidate_type_expr[get_rand_int(candidate_type_expr.size())]);
      if (expr) {
        auto tmp = new IR(kOptLimit, OPSTART("OFFSET"), deep_copy(expr));
        res.push_back(tmp);
      }
    }
    if (input->op_ == NULL || input->op_->prefix_ != "LIMIT" || input->op_->middle_ != "OFFSET") {
      auto expr1 = input->left_ != NULL ? input->left_ : get_from_libary_2D_type(candidate_type_expr[get_rand_int(candidate_type_expr.size())]);
      auto expr2 = get_from_libary_2D_type(candidate_type_expr[get_rand_int(candidate_type_expr.size())]);
      if (expr1 && expr2) {
        auto tmp = new IR(kOptLimit, OP2("LIMIT", "OFFSET"), deep_copy(expr1), deep_copy(expr2));
        res.push_back(tmp);
      }
    }
    if (input->op_ != NULL) res.push_back(new IR(kOptLimit, "LIMIT ALL"));
    if (input->op_ == NULL || input->op_->prefix_ != "LIMIT ALL OFFSET" || input->op_->middle_ != "") {
      auto expr = input->left_ != NULL ? input->left_ : get_from_libary_2D_type(candidate_type_expr[get_rand_int(candidate_type_expr.size())]);
      if (expr) {
        auto tmp = new IR(kOptLimit, OPSTART("LIMIT ALL OFFSET"), deep_copy(expr));
        res.push_back(tmp);
      }
    }
    break;
  }
  case kOptLiteralList: {
    /*
    literal_list
    (null)
    */
    if (input->left_)
      res.push_back(new IR(kOptLiteralList, string("")));
    else {
      auto new_ir = get_from_libary_2D_type(kLiteralList);
      if (new_ir) {
        auto copy = new IR(kOptLiteralList, OP0(), deep_copy(new_ir));
        res.push_back(copy);
      }
    }
    break;
  }
  case kOperand: {
    /*
    '(' expr ')'
    array_index
    scalar_expr
    unary_expr
    binary_expr
    case_expr
    function_expr
    extract_expr
    array_expr
    '(' select_no_paren ')'
    */
    if (std::find(candidate_type_expr.begin(), candidate_type_expr.end(), input->left_->type_) != candidate_type_expr.end()) {
      // case0
      auto select_no_paren = get_from_libary_2D_type(kSelectNoParen);
      if (select_no_paren) {
        auto copy = deep_copy(input);
        deep_delete(copy->left_);
        copy->left_ = deep_copy(select_no_paren);
        res.push_back(copy);
      }
      auto expr = get_from_libary_2D_type(candidate_type_operand_case1[get_rand_int(candidate_type_operand_case1.size())]);
      if (expr) {
        auto copy = deep_copy(input);
        deep_delete(copy->left_);
        copy->left_ = deep_copy(expr);
        copy->op_->prefix_ = "";
        copy->op_->middle_ = "";
        res.push_back(copy);
      }
    }
    if (std::find(candidate_type_operand_case1.begin(), candidate_type_operand_case1.end(), input->left_->type_) != candidate_type_operand_case1.end()) {
      // case0
      auto select_no_paren = get_from_libary_2D_type(kSelectNoParen);
      if (select_no_paren) {
        auto copy = deep_copy(input);
        deep_delete(copy->left_);
        copy->left_ = deep_copy(select_no_paren);
        copy->op_->prefix_ = "(";
        copy->op_->middle_ = ")";
        res.push_back(copy);
      }
      auto expr = get_from_libary_2D_type(candidate_type_expr[get_rand_int(candidate_type_expr.size())]);
      if (expr) {
        auto copy = deep_copy(input);
        deep_delete(copy->left_);
        copy->left_ = deep_copy(expr);
        copy->op_->prefix_ = "(";
        copy->op_->middle_ = ")";
        res.push_back(copy);
      }
    }
    if (input->left_->type_ == kSelectNoParen) {
      auto expr = get_from_libary_2D_type(candidate_type_operand_case1[get_rand_int(candidate_type_operand_case1.size())]);
      if (expr) {
        auto copy = deep_copy(input);
        deep_delete(copy->left_);
        copy->left_ = deep_copy(expr);
        copy->op_->prefix_ = "";
        copy->op_->middle_ = "";
        res.push_back(copy);
      }
      expr = get_from_libary_2D_type(candidate_type_expr[get_rand_int(candidate_type_expr.size())]);
      if (expr) {
        auto copy = deep_copy(input);
        deep_delete(copy->left_);
        copy->left_ = deep_copy(expr);
        res.push_back(copy);
      }
    }
    break;
  }
  case kScalarExpr: {
    /*
    column_name
    literal
    */
    if (input->left_->type_ == kColumnName) {
      auto literal = get_from_libary_2D_type(candidate_type_literal[get_rand_int(candidate_type_literal.size())]);
      if (literal) {
        auto copy = deep_copy(input);
        deep_delete(copy->left_);
        copy->left_ = deep_copy(literal);
        res.push_back(copy);
      }
    } else {
      auto column_name = get_from_libary_2D_type(kColumnName);
      if (column_name) {
        auto copy = deep_copy(input);
        deep_delete(copy->left_);
        copy->left_ = deep_copy(column_name);
        res.push_back(copy);
      }
    }
    break;
  }
  case kUnaryExpr: {
    /*
    '-' operand
    NOT operand
    operand ISNULL
    operand IS NULL
    operand IS NOT NULL
    */
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
    break;
  }
  case kBinaryExpr: {
    /*
    comp_expr
    operand '-' operand
    operand '+' operand
    operand '/' operand
    operand '*' operand
    operand '%' operand
    operand '^' operand
    operand LIKE operand
    operand NOT LIKE operand
    operand ILIKE operand
    operand CONCAT operand
    operand GLOB operand
    operand MATCH operand
    operand REGEX operand
    */
    if (input->left_->type_ != kCompExpr) {
      auto comp_expr = get_from_libary_2D_type(kCompExpr);
      if (comp_expr) {
        res.push_back(new IR(kBinaryExpr, OP0(), deep_copy(comp_expr)));
      }
    }
    if (input->op_->middle_ != "-") {
      if (input->left_->type_ == kCompExpr) {
        auto operand = get_from_libary_2D_type(kOperand);
        if (operand) {
          auto operand2 = get_from_libary_2D_type(kOperand);
          auto tmp = new IR(kBinaryExpr, OPMID("-"), deep_copy(operand), deep_copy(operand2));
          res.push_back(tmp);
        }
      } else {
        auto copy = deep_copy(input);
        copy->op_->middle_ = "-";
        res.push_back(copy);
      }
    }
    if (input->op_->middle_ != "+") {
      if (input->left_->type_ == kCompExpr) {
        auto operand = get_from_libary_2D_type(kOperand);
        if (operand) {
          auto operand2 = get_from_libary_2D_type(kOperand);
          auto tmp = new IR(kBinaryExpr, OPMID("+"), deep_copy(operand), deep_copy(operand2));
          res.push_back(tmp);
        }
      } else {
        auto copy = deep_copy(input);
        copy->op_->middle_ = "+";
        res.push_back(copy);
      }
    }
    if (input->op_->middle_ != "/") {
      if (input->left_->type_ == kCompExpr) {
        auto operand = get_from_libary_2D_type(kOperand);
        if (operand) {
          auto operand2 = get_from_libary_2D_type(kOperand);
          auto tmp = new IR(kBinaryExpr, OPMID("/"), deep_copy(operand), deep_copy(operand2));
          res.push_back(tmp);
        }
      } else {
        auto copy = deep_copy(input);
        copy->op_->middle_ = "/";
        res.push_back(copy);
      }
    }
    if (input->op_->middle_ != "*") {
      if (input->left_->type_ == kCompExpr) {
        auto operand = get_from_libary_2D_type(kOperand);
        if (operand) {
          auto operand2 = get_from_libary_2D_type(kOperand);
          auto tmp = new IR(kBinaryExpr, OPMID("*"), deep_copy(operand), deep_copy(operand2));
          res.push_back(tmp);
        }
      } else {
        auto copy = deep_copy(input);
        copy->op_->middle_ = "*";
        res.push_back(copy);
      }
    }
    if (input->op_->middle_ != "%") {
      if (input->left_->type_ == kCompExpr) {
        auto operand = get_from_libary_2D_type(kOperand);
        if (operand) {
          auto operand2 = get_from_libary_2D_type(kOperand);
          auto tmp = new IR(kBinaryExpr, OPMID("%"), deep_copy(operand), deep_copy(operand2));
          res.push_back(tmp);
        }
      } else {
        auto copy = deep_copy(input);
        copy->op_->middle_ = "%";
        res.push_back(copy);
      }
    }
    if (input->op_->middle_ != "^") {
      if (input->left_->type_ == kCompExpr) {
        auto operand = get_from_libary_2D_type(kOperand);
        if (operand) {
          auto operand2 = get_from_libary_2D_type(kOperand);
          auto tmp = new IR(kBinaryExpr, OPMID("^"), deep_copy(operand), deep_copy(operand2));
          res.push_back(tmp);
        }
      } else {
        auto copy = deep_copy(input);
        copy->op_->middle_ = "^";
        res.push_back(copy);
      }
    }
    if (input->op_->middle_ != "LIKE") {
      if (input->left_->type_ == kCompExpr) {
        auto operand = get_from_libary_2D_type(kOperand);
        if (operand) {
          auto operand2 = get_from_libary_2D_type(kOperand);
          auto tmp = new IR(kBinaryExpr, OPMID("LIKE"), deep_copy(operand), deep_copy(operand2));
          res.push_back(tmp);
        }
      } else {
        auto copy = deep_copy(input);
        copy->op_->middle_ = "LIKE";
        res.push_back(copy);
      }
    }
    if (input->op_->middle_ != "NOT LIKE") {
      if (input->left_->type_ == kCompExpr) {
        auto operand = get_from_libary_2D_type(kOperand);
        if (operand) {
          auto operand2 = get_from_libary_2D_type(kOperand);
          auto tmp = new IR(kBinaryExpr, OPMID("NOT LIKE"), deep_copy(operand), deep_copy(operand2));
          res.push_back(tmp);
        }
      } else {
        auto copy = deep_copy(input);
        copy->op_->middle_ = "NOT LIKE";
        res.push_back(copy);
      }
    }
    if (input->op_->middle_ != "ILIKE") {
      if (input->left_->type_ == kCompExpr) {
        auto operand = get_from_libary_2D_type(kOperand);
        if (operand) {
          auto operand2 = get_from_libary_2D_type(kOperand);
          auto tmp = new IR(kBinaryExpr, OPMID("ILIKE"), deep_copy(operand), deep_copy(operand2));
          res.push_back(tmp);
        }
      } else {
        auto copy = deep_copy(input);
        copy->op_->middle_ = "ILIKE";
        res.push_back(copy);
      }
    }
    if (input->op_->middle_ != "CONCAT") {
      if (input->left_->type_ == kCompExpr) {
        auto operand = get_from_libary_2D_type(kOperand);
        if (operand) {
          auto operand2 = get_from_libary_2D_type(kOperand);
          auto tmp = new IR(kBinaryExpr, OPMID("CONCAT"), deep_copy(operand), deep_copy(operand2));
          res.push_back(tmp);
        }
      } else {
        auto copy = deep_copy(input);
        copy->op_->middle_ = "CONCAT";
        res.push_back(copy);
      }
    }
    if (input->op_->middle_ != "GLOB") {
      if (input->left_->type_ == kCompExpr) {
        auto operand = get_from_libary_2D_type(kOperand);
        if (operand) {
          auto operand2 = get_from_libary_2D_type(kOperand);
          auto tmp = new IR(kBinaryExpr, OPMID("GLOB"), deep_copy(operand), deep_copy(operand2));
          res.push_back(tmp);
        }
      } else {
        auto copy = deep_copy(input);
        copy->op_->middle_ = "GLOB";
        res.push_back(copy);
      }
    }
    if (input->op_->middle_ != "MATCH") {
      if (input->left_->type_ == kCompExpr) {
        auto operand = get_from_libary_2D_type(kOperand);
        if (operand) {
          auto operand2 = get_from_libary_2D_type(kOperand);
          auto tmp = new IR(kBinaryExpr, OPMID("MATCH"), deep_copy(operand), deep_copy(operand2));
          res.push_back(tmp);
        }
      } else {
        auto copy = deep_copy(input);
        copy->op_->middle_ = "MATCH";
        res.push_back(copy);
      }
    }
    if (input->op_->middle_ != "REGEX") {
      if (input->left_->type_ == kCompExpr) {
        auto operand = get_from_libary_2D_type(kOperand);
        if (operand) {
          auto operand2 = get_from_libary_2D_type(kOperand);
          auto tmp = new IR(kBinaryExpr, OPMID("REGEX"), deep_copy(operand), deep_copy(operand2));
          res.push_back(tmp);
        }
      } else {
        auto copy = deep_copy(input);
        copy->op_->middle_ = "REGEX";
        res.push_back(copy);
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
    operand IN '(' expr_list ')'
    operand NOT IN '(' expr_list ')'
    operand IN '(' select_no_paren ')'
    operand NOT IN '(' select_no_paren ')'
    */
    auto copy = deep_copy(input);
    copy->op_->middle_ = copy->op_->middle_ == "IN" ? "NOT IN" : "IN";  // change op_->middle
    res.push_back(copy);
    auto new_ir = get_from_libary_2D_type(copy->right_->left_->type_ == kExprList ? kSelectNoParen : kExprList);
    if (new_ir) {
      copy = deep_copy(copy);
      deep_delete(copy->right_->left_);
      copy->right_->left_ = deep_copy(new_ir);
      res.push_back(copy);
      copy = deep_copy(input);
      deep_delete(copy->right_->left_);
      copy->right_->left_ = deep_copy(new_ir);
      res.push_back(copy);
    }
    break;
  }
  case kCaseExpr: {
    /*
    CASE expr case_list END
    CASE expr case_list ELSE expr END
    CASE case_list END
    CASE case_list ELSE expr END
    All mutations use genetic variants.
    */
    if (input->op_->middle_ != "" || input->right_ == NULL) {
      if (input->left_->type_ != kUnknown) {
        auto case_expr = get_from_libary_2D_type(candidate_type_expr[get_rand_int(candidate_type_expr.size())]);
        if (case_expr) {
          auto case_list = input->left_;
          auto tmp = new IR(kCaseExpr, OP3("CASE", "", "END"), deep_copy(case_expr), deep_copy(case_list));
          res.push_back(tmp);
        }
      } else {
        auto case_expr = input->left_->left_;
        auto case_list = input->left_->right_;
        auto tmp = new IR(kCaseExpr, OP3("CASE", "", "END"), deep_copy(case_expr), deep_copy(case_list));
        res.push_back(tmp);
      }
    }
    if (input->left_->type_ != kUnknown) {
      if (input->left_->type_ != kCaseList) {
        auto case_expr1 = input->left_;
        auto case_list = input->right_;
        auto case_expr2 = get_from_libary_2D_type(candidate_type_expr[get_rand_int(candidate_type_expr.size())]);
        if (case_expr2) {
          auto tmp = new IR(kUnknown, OP0(), deep_copy(case_expr1), deep_copy(case_list));
          tmp = new IR(kCaseExpr, OP3("CASE", "ELSE", "END"), tmp, deep_copy(case_expr2));
          res.push_back(tmp);
        }
      } else {
        auto case_expr1 = get_from_libary_2D_type(candidate_type_expr[get_rand_int(candidate_type_expr.size())]);
        auto case_list = input->left_;
        auto case_expr2 = get_from_libary_2D_type(candidate_type_expr[get_rand_int(candidate_type_expr.size())]);
        if (case_expr1 && case_expr2) {
          auto tmp = new IR(kUnknown, OP0(), deep_copy(case_expr1), deep_copy(case_list));
          tmp = new IR(kCaseExpr, OP3("CASE", "ELSE", "END"), tmp, deep_copy(case_expr2));
          res.push_back(tmp);
        }
      }
    }
    if (input->right_ != NULL) {
      if (input->op_->middle_ == "") {
        auto case_list = input->right_;
        auto tmp = new IR(kCaseExpr, OP3("CASE", "", "END"), deep_copy(case_list));
        res.push_back(tmp);
      }
      if (input->left_->type_ == kUnknown) {
        auto case_list = input->left_->right_;
        auto tmp = new IR(kCaseExpr, OP3("CASE", "", "END"), deep_copy(case_list));
        res.push_back(tmp);
      }
      if (input->left_->type_ == kCaseList) {
        auto case_list = input->left_;
        auto tmp = new IR(kCaseExpr, OP3("CASE", "", "END"), deep_copy(case_list));
        res.push_back(tmp);
      }
    }
    if (input->op_->middle_ != "ELSE" || input->left_->type_ != kCaseList) {
      if (input->right_ != NULL && input->right_->type_ == kCaseList) {
        auto case_list = input->right_;
        auto case_expr = input->left_;
        auto tmp = new IR(kCaseExpr, OP3("CASE", "ELSE", "END"), deep_copy(case_list), deep_copy(case_expr));
        res.push_back(tmp);
      }
      if (input->left_->type_ == kUnknown) {
        auto case_list = input->left_->right_;
        auto case_expr = input->right_;
        auto tmp = new IR(kCaseExpr, OP3("CASE", "ELSE", "END"), deep_copy(case_list), deep_copy(case_expr));
        res.push_back(tmp);
      }
      if (input->right_ == NULL) {
        auto case_list = input->left_;
        auto case_expr = get_from_libary_2D_type(candidate_type_expr[get_rand_int(candidate_type_expr.size())]);
        if (case_expr) {
          auto tmp = new IR(kCaseExpr, OP3("CASE", "ELSE", "END"), deep_copy(case_list), deep_copy(case_expr));
          res.push_back(tmp);
        }
      }
    }
    break;
  }
  case kExistsExpr: {
    /*
    EXISTS '(' select_no_paren ')'
    NOT EXISTS '(' select_no_paren ')'
    */
    if (input->op_->prefix_ != "EXISTS") {
      auto copy = deep_copy(input);
      copy->op_->prefix_ = "EXISTS";
      res.push_back(copy);
    }
    if (input->op_->prefix_ != "NOT EXISTS") {
      auto copy = deep_copy(input);
      copy->op_->prefix_ = "NOT EXISTS";
      res.push_back(copy);
    }
    break;
  }
  case kCompExpr: {
    /*
    operand '=' operand
    operand EQUALS operand
    operand NOTEQUALS operand
    operand '<' operand
    operand '>' operand
    operand LESSEQ operand
    operand GREATEREQ operand
    */
    if (input->op_->middle_ != "=") {
      auto copy = deep_copy(input);
      copy->op_->middle_ = "=";
      res.push_back(copy);
    }
    if (input->op_->middle_ != "==") {
      auto copy = deep_copy(input);
      copy->op_->middle_ = "==";
      res.push_back(copy);
    }
    if (input->op_->middle_ != "!=") {
      auto copy = deep_copy(input);
      copy->op_->middle_ = "!=";
      res.push_back(copy);
    }
    if (input->op_->middle_ != "<") {
      auto copy = deep_copy(input);
      copy->op_->middle_ = "<";
      res.push_back(copy);
    }
    if (input->op_->middle_ != ">") {
      auto copy = deep_copy(input);
      copy->op_->middle_ = ">";
      res.push_back(copy);
    }
    if (input->op_->middle_ != "<=") {
      auto copy = deep_copy(input);
      copy->op_->middle_ = "<=";
      res.push_back(copy);
    }
    if (input->op_->middle_ != ">=") {
      auto copy = deep_copy(input);
      copy->op_->middle_ = ">=";
      res.push_back(copy);
    }
    break;
  }
  case kFunctionExpr: {
    /*
    IDENTIFIER '(' ')' opt_filter_clause opt_over_clause
    IDENTIFIER '(' opt_distinct expr_list ')' opt_filter_clause opt_over_clause
    */
    if (input->left_->left_->right_ == NULL) {
      auto opt_distinct = get_from_libary_2D_type(kOptDistinct);
      auto expr_list = get_from_libary_2D_type(kExprList);
      if (opt_distinct && expr_list) {
        auto copy = deep_copy(input);
        copy->left_->left_->right_ = new IR(kUnknown, OP3("(", "", ")"), deep_copy(opt_distinct), deep_copy(expr_list));
        copy->left_->left_->op_->middle_ = "";
        copy->left_->left_->operand_num_ = 2;
        res.push_back(copy);
      }
    } else {
      auto copy = deep_copy(input);
      deep_delete(copy->left_->left_->right_);
      copy->left_->left_->right_ = NULL;
      copy->left_->left_->op_->middle_ = "()";
      copy->left_->left_->operand_num_ = 1;
      res.push_back(copy);
    }
    break;
  }
  case kOptOverClause: {
    /*
    OVER '(' window ')'
    OVER IDENTIFIER
    (null)
    */
    if (input->left_ != NULL) {
      res.push_back(new IR(kOptOverClause, string("")));
      if (input->op_->middle_ == ")") {
        auto id = get_from_libary_2D_type(kIdentifier);
        if (id) {
          auto tmp = new IR(kOptOverClause, OP1("OVER"), deep_copy(id));
          tmp->left_->id_type_ = id_window_name;
          res.push_back(tmp);
        }
      } else {
        auto window = get_from_libary_2D_type(kWindow);
        if (window) {
          auto tmp = new IR(kOptOverClause, OP2("OVER(", ")"), deep_copy(window));
          res.push_back(tmp);
        }
      }
    } else {
      auto id = get_from_libary_2D_type(kIdentifier);
      if (id) {
        auto tmp = new IR(kOptOverClause, OP1("OVER"), deep_copy(id));
        tmp->left_->id_type_ = id_window_name;
        res.push_back(tmp);
      }
      auto window = get_from_libary_2D_type(kWindow);
      if (window) {
        auto tmp = new IR(kOptOverClause, OP2("OVER(", ")"), deep_copy(window));
        res.push_back(tmp);
      }
    }
    break;
  }
  case kOptFilterClause: {
    /*
    FILTER '(' WHERE expr ')'
    (null)
    */
    if (input->left_)
      res.push_back(new IR(kOptFilterClause, string("")));
    else {
      auto new_ir = get_from_libary_2D_type(candidate_type_expr[get_rand_int(candidate_type_expr.size())]);
      if (new_ir) {
        auto copy = new IR(kOptFilterClause, OP2("FILTER( WHEN", ")"), deep_copy(new_ir));
        res.push_back(copy);
      }
    }
    break;
  }
  case kDatetimeField: {
    /*
    SECOND
    MINUTE
    HOUR
    DAY
    MONTH
    YEAR
    */
    if (input->str_val_ != "SECOND") {
      auto copy = deep_copy(input);
      copy->str_val_ = "SECOND";
      res.push_back(copy);
    }
    if (input->str_val_ != "MINUTE") {
      auto copy = deep_copy(input);
      copy->str_val_ = "MINUTE";
      res.push_back(copy);
    }
    if (input->str_val_ != "HOUR") {
      auto copy = deep_copy(input);
      copy->str_val_ = "HOUR";
      res.push_back(copy);
    }
    if (input->str_val_ != "DAY") {
      auto copy = deep_copy(input);
      copy->str_val_ = "DAY";
      res.push_back(copy);
    }
    if (input->str_val_ != "MONTH") {
      auto copy = deep_copy(input);
      copy->str_val_ = "MONTH";
      res.push_back(copy);
    }
    if (input->str_val_ != "YEAR") {
      auto copy = deep_copy(input);
      copy->str_val_ = "YEAR";
      res.push_back(copy);
    }
    break;
  }
  case kColumnName: {
    /*
    IDENTIFIER
    IDENTIFIER '.' IDENTIFIER
    '*'
    IDENTIFIER '.' '*'
    */
    if (input->left_ != NULL && input->right_ == NULL) {
      auto identifier = get_from_libary_2D_type(kIdentifier);
      auto identifier1_copy = deep_copy(identifier);
      auto identifier2_copy = deep_copy(identifier);
      identifier1_copy->id_type_ = id_whatever;
      identifier2_copy->id_type_ = id_whatever;
      auto tmp = new IR(kColumnName, OPMID("."), identifier1_copy, identifier2_copy);
      tmp->id_type_ = id_column_name;
      res.push_back(tmp);
      res.push_back(new IR(kColumnName, string("*")));
      identifier = get_from_libary_2D_type(kIdentifier);
      auto identifier_copy = deep_copy(identifier);
      identifier_copy->id_type_ = id_whatever;
      tmp = new IR(kconst_str, string("*"));
      tmp = new IR(kColumnName, OPMID("."), identifier_copy, tmp);
      tmp->id_type_ = id_column_name;
      res.push_back(tmp);
    }
    if (input->op_ && input->op_->middle_ == "." && input->right_->type_ == kIdentifier) {
      auto identifier = get_from_libary_2D_type(kIdentifier);
      auto identifier_copy = deep_copy(identifier);
      identifier_copy->id_type_ = id_column_name;
      auto tmp = new IR(kColumnName, OP0(), identifier_copy);
      res.push_back(tmp);
      res.push_back(new IR(kColumnName, string("*")));
      identifier_copy = deep_copy(identifier);
      identifier_copy->id_type_ = id_whatever;
      tmp = new IR(kconst_str, string("*"));
      tmp = new IR(kColumnName, OPMID("."), identifier_copy, tmp);
      tmp->id_type_ = id_column_name;
      res.push_back(tmp);
    }
    if (input->op_ == NULL) {
      auto identifier = get_from_libary_2D_type(kIdentifier);
      auto identifier_copy = deep_copy(identifier);
      identifier_copy->id_type_ = id_column_name;
      auto tmp = new IR(kColumnName, OP0(), identifier_copy);
      res.push_back(tmp);
      auto identifier1_copy = deep_copy(identifier);
      auto identifier2_copy = deep_copy(identifier);
      identifier1_copy->id_type_ = id_whatever;
      identifier2_copy->id_type_ = id_whatever;
      tmp = new IR(kColumnName, OPMID("."), identifier1_copy, identifier2_copy);
      tmp->id_type_ = id_column_name;
      res.push_back(tmp);
      identifier_copy = deep_copy(identifier);
      identifier_copy->id_type_ = id_whatever;
      tmp = new IR(kconst_str, string("*"));
      tmp = new IR(kColumnName, OPMID("."), identifier_copy, tmp);
      tmp->id_type_ = id_column_name;
      res.push_back(tmp);
    }
    if (input->op_ && input->op_->middle_ == "." && input->right_->type_ == kconst_str) {
      auto identifier = get_from_libary_2D_type(kIdentifier);
      auto identifier_copy = deep_copy(identifier);
      identifier_copy->id_type_ = id_column_name;
      auto tmp = new IR(kColumnName, OP0(), identifier_copy);
      res.push_back(tmp);
      auto identifier1_copy = deep_copy(identifier);
      auto identifier2_copy = deep_copy(identifier);
      identifier1_copy->id_type_ = id_whatever;
      identifier2_copy->id_type_ = id_whatever;
      tmp = new IR(kColumnName, OPMID("."), identifier1_copy, identifier2_copy);
      tmp->id_type_ = id_column_name;
      res.push_back(tmp);
      res.push_back(new IR(kColumnName, string("*")));
    }
    break;
  }
  case kBoolLiteral: {
    /*
    TRUE
    FALSE
    */
    if (input->b_val_ != true) {
      auto copy = deep_copy(input);
      copy->b_val_ = true;
      res.push_back(copy);
    }
    if (input->b_val_ != false) {
      auto copy = deep_copy(input);
      copy->b_val_ = false;
      res.push_back(copy);
    }
    break;
  }
  case kTableRef: {
    /*
    table_prefix table_name opt_alias opt_index opt_on opt_using
    table_prefix table_name '(' expr_list ')' opt_alias opt_on opt_using
    table_prefix '(' select_no_paren ')' opt_alias opt_on opt_using
    table_prefix '(' table_ref ')' opt_alias opt_on opt_using
    */
    if (input->left_->left_->right_->type_ != kOptIndex) {
      auto opt_using = input->right_;
      auto opt_on = input->left_->right_;
      auto opt_alias = input->left_->left_->right_;
      auto table_name = input->left_->left_->left_->left_->type_ == kUnknown ? input->left_->left_->left_->left_->right_ : get_from_libary_2D_type(kTableName);
      auto table_prefix = input->left_->left_->left_->left_->type_ == kUnknown ? input->left_->left_->left_->left_->left_ : input->left_->left_->left_->left_;
      auto opt_index = get_from_libary_2D_type(kOptIndex);
      if (table_name && opt_index) {
        auto table_name_copy = deep_copy(table_name);
        table_name_copy->id_type_ = id_top_table_name;
        auto tmp = new IR(kUnknown, OP0(), deep_copy(table_prefix), table_name_copy);
        tmp = new IR(kUnknown, OP0(), tmp, deep_copy(opt_alias));
        tmp = new IR(kUnknown, OP0(), tmp, deep_copy(opt_index));
        tmp = new IR(kUnknown, OP0(), tmp, deep_copy(opt_on));
        tmp = new IR(kTableRef, OP0(), tmp, deep_copy(opt_using));
        res.push_back(tmp);
      }
    }
    if (input->left_->left_->left_->right_->type_ != kExprList) {
      auto opt_using = input->right_;
      auto opt_on = input->left_->right_;
      auto opt_alias = input->left_->left_->right_->type_ == kOptAlias ? input->left_->left_->right_ : input->left_->left_->left_->right_;
      auto expr_list = get_from_libary_2D_type(kExprList);
      auto table_name = input->left_->left_->left_->left_->type_ == kUnknown ? input->left_->left_->left_->left_->right_ : get_from_libary_2D_type(kTableName);
      auto table_prefix = input->left_->left_->left_->left_->type_ == kUnknown ? input->left_->left_->left_->left_->left_ : input->left_->left_->left_->left_;
      if (expr_list) {
        auto table_name_copy = deep_copy(table_name);
        table_name_copy->id_type_ = id_top_table_name;
        auto tmp = new IR(kUnknown, OP0(), deep_copy(table_prefix), table_name_copy);
        tmp = new IR(kUnknown, OP3("", "(", ")"), tmp, deep_copy(expr_list));
        tmp = new IR(kUnknown, OP0(), tmp, deep_copy(opt_alias));
        tmp = new IR(kUnknown, OP0(), tmp, deep_copy(opt_on));
        tmp = new IR(kTableRef, OP0(), tmp, deep_copy(opt_using));
        res.push_back(tmp);
      }
    }
    if (input->left_->left_->left_->right_->type_ != kSelectNoParen) {
      auto opt_using = input->right_;
      auto opt_on = input->left_->right_;
      auto opt_alias = input->left_->left_->right_->type_ == kOptAlias ? input->left_->left_->right_ : input->left_->left_->left_->right_;
      auto select_no_paren = get_from_libary_2D_type(kSelectNoParen);
      auto table_prefix = input->left_->left_->left_->left_->type_ == kUnknown ? input->left_->left_->left_->left_->left_ : input->left_->left_->left_->left_;
      if (select_no_paren) {
        auto tmp = new IR(kUnknown, OP3("", "(", ")"), deep_copy(table_prefix), deep_copy(select_no_paren));
        tmp = new IR(kUnknown, OP0(), tmp, deep_copy(opt_alias));
        tmp = new IR(kUnknown, OP0(), tmp, deep_copy(opt_on));
        tmp = new IR(kTableRef, OP0(), tmp, deep_copy(opt_using));
        res.push_back(tmp);
      }
    }
    if (input->left_->left_->left_->right_->type_ != kTableRef) {
      auto opt_using = input->right_;
      auto opt_on = input->left_->right_;
      auto opt_alias = input->left_->left_->right_->type_ == kOptAlias ? input->left_->left_->right_ : input->left_->left_->left_->right_;
      auto table_ref = get_from_libary_2D_type(kTableRef);
      auto table_prefix = input->left_->left_->left_->left_->type_ == kUnknown ? input->left_->left_->left_->left_->left_ : input->left_->left_->left_->left_;
      if (table_ref) {
        auto tmp = new IR(kUnknown, OP3("", "(", ")"), deep_copy(table_prefix), deep_copy(table_ref));
        tmp = new IR(kUnknown, OP0(), tmp, deep_copy(opt_alias));
        tmp = new IR(kUnknown, OP0(), tmp, deep_copy(opt_on));
        tmp = new IR(kTableRef, OP0(), tmp, deep_copy(opt_using));
        res.push_back(tmp);
      }
    }
    break;
  }
  case kTablePrefix: {
    /*
    table_ref join_op
    (null)
    */
    if (input->left_)
      res.push_back(new IR(kTablePrefix, string("")));
    else {
      auto table_ref = get_from_libary_2D_type(kTableRef);
      auto join_op = get_from_libary_2D_type(kJoinOp);
      if (table_ref && join_op) {
        auto copy = new IR(kTablePrefix, OP0(), deep_copy(table_ref), deep_copy(join_op));
        res.push_back(copy);
      }
    }
    break;
  }
  case kJoinOp: {
    /*
    ','
    JOIN
    join_kw JOIN
    join_kw IDENTIFIER JOIN
    join_kw IDENTIFIER IDENTIFIER JOIN
    */
    if (input->left_ != NULL || input->str_val_ != ",") {
      res.push_back(new IR(kJoinOp, string(",")));
    }
    if (input->left_ != NULL || input->str_val_ != "JOIN") {
      res.push_back(new IR(kJoinOp, string("JOIN")));
    }
    if (input->left_ == NULL || input->right_ != NULL) {
      if (input->left_ == NULL) {
        auto join_kw = get_from_libary_2D_type(kJoinKw);
        if (join_kw) {
          auto tmp = new IR(kJoinOp, OPEND("JOIN"), deep_copy(join_kw));
          res.push_back(tmp);
        }
      } else {
        auto join_kw = input->left_;
        auto tmp = new IR(kJoinOp, OPEND("JOIN"), deep_copy(join_kw));
        res.push_back(tmp);
      }
    }
    if (input->left_ == NULL || input->right_ == NULL || input->right_->type_ != kIdentifier) {
      if (input->left_ == NULL) {
        auto join_kw = get_from_libary_2D_type(kJoinKw);
        auto id = get_from_libary_2D_type(kIdentifier);
        if (join_kw && id) {
          auto id_copy = deep_copy(id);
          id_copy->id_type_ = id_top_table_name;
          auto tmp = new IR(kJoinOp, OPEND("JOIN"), deep_copy(join_kw), id_copy);
          res.push_back(tmp);
        }
      } else if (input->left_ != NULL && input->right_ == NULL) {
        auto join_kw = input->left_;
        auto id = get_from_libary_2D_type(kIdentifier);
        if (id) {
          auto id_copy = deep_copy(id);
          id_copy->id_type_ = id_top_table_name;
          auto tmp = new IR(kJoinOp, OPEND("JOIN"), deep_copy(join_kw), id_copy);
          res.push_back(tmp);
        }
      } else {
        auto join_kw = input->left_;
        auto id = input->right_->left_;
        auto id_copy = deep_copy(id);
        id_copy->id_type_ = id_top_table_name;
        auto tmp = new IR(kJoinOp, OPEND("JOIN"), deep_copy(join_kw), id_copy);
        res.push_back(tmp);
      }
    }
    if (input->left_ == NULL || input->right_ == NULL || input->right_->type_ != kUnknown) {
      if (input->left_ == NULL) {
        auto join_kw = get_from_libary_2D_type(kJoinKw);
        auto id = get_from_libary_2D_type(kIdentifier);
        if (join_kw && id) {
          auto tmp = new IR(kJoinOp, OPEND("JOIN"), deep_copy(id), deep_copy(id));
          tmp = new IR(kJoinOp, OPEND("JOIN"), deep_copy(join_kw), tmp);
          res.push_back(tmp);
        }
      } else {
        auto join_kw = input->left_;
        auto id = input->right_ != NULL ? input->right_ : get_from_libary_2D_type(kIdentifier);
        if (id) {
          auto tmp = new IR(kJoinOp, OPEND("JOIN"), deep_copy(id), deep_copy(id));
          tmp = new IR(kJoinOp, OPEND("JOIN"), deep_copy(join_kw), tmp);
          res.push_back(tmp);
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
    if (input->left_ == NULL) {
      auto column_name = get_from_libary_2D_type(kColumnName);
      if (column_name) {
        auto tmp = new IR(kOptIndex, OP1("INDEXED BY"), deep_copy(column_name));
        res.push_back(tmp);
      }
    }
    if (input->left_ != NULL || input->str_val_ != "NOT INDEXED") {
      res.push_back(new IR(kOptIndex, string("NOT INDEXED")));
    }
    if (input->left_ != NULL || input->str_val_ != "") {
      res.push_back(new IR(kOptIndex, string("")));
    }
    break;
  }
  case kOptOn: {
    /*
    ON expr
    (null)
    */
    if (input->left_)
      res.push_back(new IR(kOptOn, string("")));
    else {
      auto new_ir = get_from_libary_2D_type(candidate_type_expr[get_rand_int(candidate_type_expr.size())]);
      if (new_ir) {
        auto copy = new IR(kOptOn, OP1("ON"), deep_copy(new_ir));
        res.push_back(copy);
      }
    }
    break;
  }
  case kOptUsing: {
    /*
    USING '(' ident_commalist ')'
    (null)
    */
    if (input->left_)
      res.push_back(new IR(kOptUsing, string("")));
    else {
      auto new_ir = get_from_libary_2D_type(kIdentCommaList);
      if (new_ir) {
        auto copy = new IR(kOptUsing, OP3("USING", "(", ")"), NULL, deep_copy(new_ir));
        res.push_back(copy);
      }
    }
    break;
  }
  case kTableName: {
    /*
    IDENTIFIER
    IDENTIFIER '.' IDENTIFIER
    */
    if (input->right_ == NULL) {
      auto copy = deep_copy(input);
      copy->right_ = deep_copy(input->left_);
      copy->op_->middle_ = ".";
      copy->operand_num_ = 2;
      copy->left_->id_type_ = id_database_name;
      copy->right_->id_type_ = id_table_name;
      res.push_back(copy);
    } else {
      auto id_copy = deep_copy(input->right_);
      id_copy->id_type_ = id_table_name;
      auto tmp = new IR(kTableName, OP0(), id_copy);
      res.push_back(tmp);
    }
    break;
  }
  case kOptAlias: {
    /*
    alias
    (null)
    */
    if (input->left_)
      res.push_back(new IR(kOptAlias, string("")));
    else {
      auto new_ir = get_from_libary_2D_type(kAlias);
      if (new_ir) {
        auto copy = new IR(kOptAlias, OP0(), deep_copy(new_ir));
        res.push_back(copy);
      }
    }
    break;
  }
  case kOptWithClause: {
    /*
    with_clause
    (null)
    */
    if (input->left_)
      res.push_back(new IR(kOptWithClause, string("")));
    else {
      auto new_ir = get_from_libary_2D_type(kWithClause);
      if (new_ir) {
        auto copy = new IR(kOptWithClause, OP0(), deep_copy(new_ir));
        res.push_back(copy);
      }
    }
    break;
  }
  case kJoinKw: {
    /*
    INNER
    LEFT OUTER
    LEFT
    RIGHT OUTER
    RIGHT
    FULL OUTER
    OUTER
    FULL
    CROSS
    NATURAL
    */
    if (input->str_val_ != "INNER") {
      auto copy = deep_copy(input);
      copy->str_val_ = "INNER";
      res.push_back(copy);
    }
    if (input->str_val_ != "LEFT OUTER") {
      auto copy = deep_copy(input);
      copy->str_val_ = "LEFT OUTER";
      res.push_back(copy);
    }
    if (input->str_val_ != "LEFT") {
      auto copy = deep_copy(input);
      copy->str_val_ = "LEFT";
      res.push_back(copy);
    }
    if (input->str_val_ != "RIGHT OUTER") {
      auto copy = deep_copy(input);
      copy->str_val_ = "RIGHT OUTER";
      res.push_back(copy);
    }
    if (input->str_val_ != "RIGHT") {
      auto copy = deep_copy(input);
      copy->str_val_ = "RIGHT";
      res.push_back(copy);
    }
    if (input->str_val_ != "FULL OUTER") {
      auto copy = deep_copy(input);
      copy->str_val_ = "FULL OUTER";
      res.push_back(copy);
    }
    if (input->str_val_ != "OUTER") {
      auto copy = deep_copy(input);
      copy->str_val_ = "OUTER";
      res.push_back(copy);
    }
    if (input->str_val_ != "FULL") {
      auto copy = deep_copy(input);
      copy->str_val_ = "FULL";
      res.push_back(copy);
    }
    if (input->str_val_ != "CROSS") {
      auto copy = deep_copy(input);
      copy->str_val_ = "CROSS";
      res.push_back(copy);
    }
    if (input->str_val_ != "NATURAL") {
      auto copy = deep_copy(input);
      copy->str_val_ = "NATURAL";
      res.push_back(copy);
    }
    break;
  }
  case kOptSemicolon: {
    /*
    ';'
    (null)
    */
    if (input->str_val_ != ",") {
      auto copy = deep_copy(input);
      copy->str_val_ = ",";
      res.push_back(copy);
    }
    if (input->str_val_ != "") {
      auto copy = deep_copy(input);
      copy->str_val_ = "";
      res.push_back(copy);
    }
    break;
  }
  default:
    break;
  }

  input->mutated_times_ += res.size();
  for (auto i : res) {
    if (i == NULL) continue;
    i->mutated_times_ = input->mutated_times_;
    add_to_library_no_traverse(i);
  }
  return res;
}

void Mutator::init(string f_testcase, string f_common_string, string pragma) {
  ifstream input_test(f_testcase);
  string line;

  // init lib from multiple sql
  while (getline(input_test, line)) {
    auto p = parser(line);
    if (p == NULL) continue;

    vector<IR *> v_ir;
    auto res = p->translate(v_ir);
    p->deep_delete();
    p = NULL;
    string strip_sql = extract_struct(res);
    deep_delete(res);
    p = parser(strip_sql);

    if (p == NULL) continue;

    res = p->translate(v_ir);
    p->deep_delete();
    p = NULL;
    add_to_library(res);
    deep_delete(res);
  }

  // init utils::m_tables
  vector<string> v_tmp = {"haha1", "haha2", "haha3"};
  v_table_names.insert(v_table_names.end(), v_tmp.begin(), v_tmp.end());
  m_tables["haha1"] = {"ducking_column0_1", "ducking_column1_1",
                       "ducking_column2_1"};
  m_tables["haha2"] = {"ducking_column0_2", "ducking_column1_2",
                       "ducking_column2_2"};
  m_tables["haha3"] = {"ducking_column0_3", "ducking_column1_3",
                       "ducking_column2_3"};

  // init value_libary
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

  value_libary.insert(value_libary.begin(), value_lib_init.begin(),
                      value_lib_init.end());

  // init common_string_libary
  common_string_libary.push_back("DO_NOT_BE_EMPTY");
  if (f_common_string != "") {
    ifstream input_string(f_common_string);
    string s;

    while (getline(input_string, s)) {
      common_string_libary.push_back(s);
    }
  }
  string_libary.push_back("x");
  string_libary.push_back("v0");
  string_libary.push_back("v1");

  ifstream input_pragma(pragma);
  assert(input_pragma.is_open());
  string s;
  std::cout << "[duck]start init pragma" << std::endl;
  while (getline(input_pragma, s)) {
    if (s.empty()) continue;

    auto pos = s.find('=');
    if (pos == string::npos) continue;
    string k = s.substr(0, pos - 1);
    string v = s.substr(pos + 2);
    if (find(cmds_.begin(), cmds_.end(), k) == cmds_.end()) {
      cmds_.push_back(k);
      std::cout << "Pushing: " << s << std::endl;
    }
    m_cmd_value_lib_[k].push_back(v);
  }

  assert(!cmds_.empty());
  relationmap[id_column_name] = id_top_table_name;
  relationmap[id_table_name] = id_top_table_name;
  relationmap[id_index_name] = id_top_table_name;
  relationmap[id_create_column_name] = id_create_table_name;
  relationmap[id_pragma_value] = id_pragma_name;
  cross_map[id_top_table_name] = id_create_table_name;

  identifier_type.insert({kSavepointName, kSchemaName, kPragmaName, kCollationName, kTriggerName, kModuleName});
  single_grammar_expression.insert({kRollbackStatement, kIndexedColumn, kAssignClause, kPrepareStatement,
                                    kPrepareTargetQuery, kImportStatement,kImportFileType, kFilePath,
                                    kTriggerDeclare, kTriggerCmd,kColumnDef, kDeleteStatement, kUpdateStatement,
                                    kUpdateClause,kSetOperator, kWindowClause, kWindowDefn, kSelectList,
                                    kFromClause, kOrderDesc, kExprAlias, kCastExpr, kExtractExpr, kArrayExpr,
                                    kArrayIndex, kBetweenExpr, kStringLiteral, kIntLiteral, kNullLiteral,
                                    kParamExpr, kTableRefNameNoAlias, kAlias, kWithClause, kWithDescription});
  list_type.insert({kStatementList, kIndexedColumnList, kAssignList, kColumnNameList, kHintList, kTriggerCmdList,
                    kColumnDefCommaList, kColumnArglist, kSuperList, kUpdateClauseCommalist, kWindowDefnList,
                    kSelectList, kOrderList, kExprList, kLiteralList, kCaseList, kWithDescriptionList, kIdentCommaList});
  return;
}

vector<IR *> Mutator::mutate(IR *input) {
  vector<IR *> res;

  if (!lucky_enough_to_be_mutated(input->mutated_times_)) {
    return res;  // return a empty set if the IR is not mutated
  }

  res.push_back(strategy_delete(input));
  res.push_back(strategy_insert(input));
  res.push_back(strategy_replace(input));

  // may do some simple filter for res, like removing some duplicated cases

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

string Mutator::validate(IR *root) {
  if (root == NULL) return "";
  try {
    string sql_str = root->to_string();
    auto parsed_ir = parser(sql_str);
    if (parsed_ir == NULL) return "";
    parsed_ir->deep_delete();

    reset_counter();
    vector<IR *> ordered_ir;
    auto graph =
        build_dependency_graph(root, relationmap, cross_map, ordered_ir);
    fix_graph(graph, root, ordered_ir);
    return fix(root);
  } catch (...) {
    // invalid sql , skip
  }
  return "";
}

static void collect_ir(IR *root, set<IDTYPE> &type_to_fix,
                       vector<IR *> &ir_to_fix) {
  auto idtype = root->id_type_;

  if (root->left_) {
    collect_ir(root->left_, type_to_fix, ir_to_fix);
  }

  if (type_to_fix.find(idtype) != type_to_fix.end()) {
    ir_to_fix.push_back(root);
  }

  if (root->right_) {
    collect_ir(root->right_, type_to_fix, ir_to_fix);
  }
}

static IR *search_mapped_ir(IR *ir, IDTYPE idtype) {
  vector<IR *> to_search;
  vector<IR *> backup;
  to_search.push_back(ir);
  while (!to_search.empty()) {
    for (auto i : to_search) {
      if (i->id_type_ == idtype) {
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

void cross_stmt_map(map<IR *, set<IR *>> &graph, vector<IR *> &ir_to_fix,
                    map<IDTYPE, IDTYPE> &cross_map) {
  for (auto m : cross_map) {
    vector<IR *> value;
    vector<IR *> key;

    for (auto &k : graph) {
      if (k.first->id_type_ == m.first) {
        key.push_back(k.first);
      }
    }

    for (auto &k : ir_to_fix) {
      if (k->id_type_ == m.second) {
        value.push_back(k);
      }
    }

    if (key.empty()) return;
    for (auto val : value) {
      graph[key[get_rand_int(key.size())]].insert(val);
    }
  }
}

void toptable_map(map<IR *, set<IR *>> &graph, vector<IR *> &ir_to_fix,
                  vector<IR *> &toptable) {
  vector<IR *> tablename;
  for (auto ir : ir_to_fix) {
    if (ir->id_type_ == id_table_name) {
      tablename.push_back(ir);
    } else if (ir->id_type_ == id_top_table_name) {
      toptable.push_back(ir);
    }
  }
  if (toptable.empty()) return;
  for (auto k : tablename) {
    auto r = get_rand_int(toptable.size());
    graph[toptable[r]].insert(k);
  }
}

vector<IR *> Mutator::extract_statement(IR *root) {
  vector<IR *> res;
  deque<IR *> bfs = {root};

  while (bfs.empty() != true) {
    auto node = bfs.front();
    bfs.pop_front();

    if (node->type_ == kStatement) res.push_back(node);
    if (node->left_) bfs.push_back(node->left_);
    if (node->right_) bfs.push_back(node->right_);
  }

  return res;
}

vector<IR *> Mutator::cut_subquery(IR *program, map<IR **, IR *> &m_save) {
  vector<IR *> res;
  vector<IR *> v_statements;
  deque<IR *> dfs = {program};

  while (dfs.empty() != true) {
    auto node = dfs.front();
    dfs.pop_front();

    if (node->type_ == kStatement) v_statements.push_back(node);
    if (node->left_) dfs.push_back(node->left_);
    if (node->right_) dfs.push_back(node->right_);
  }

  reverse(v_statements.begin(), v_statements.end());
  for (auto &stmt : v_statements) {
    deque<IR *> q_bfs = {stmt};
    res.push_back(stmt);

    while (!q_bfs.empty()) {
      auto cur = q_bfs.front();
      q_bfs.pop_front();

      if (cur->left_) {
        q_bfs.push_back(cur->left_);
        if (cur->left_->type_ == kSelectNoParen) {
          res.push_back(cur->left_);
          m_save[&cur->left_] = cur->left_;
          cur->left_ = NULL;
        }
      }

      if (cur->right_) {
        q_bfs.push_back(cur->right_);
        if (cur->right_->type_ == kSelectNoParen) {
          res.push_back(cur->right_);
          m_save[&cur->right_] = cur->right_;
          cur->right_ = NULL;
        }
      }
    }
  }
  return res;
}

bool Mutator::fix_back(map<IR **, IR *> &m_save) {
  for (auto &i : m_save) {
    if (*(i.first) != NULL) return false;
    *(i.first) = i.second;
  }

  return true;
}

map<IR *, set<IR *>> Mutator::build_dependency_graph(
    IR *root, map<IDTYPE, IDTYPE> &relationmap, map<IDTYPE, IDTYPE> &cross_map,
    vector<IR *> &ordered_ir) {
  map<IR *, set<IR *>> graph;
  set<IDTYPE> type_to_fix;
  map<IR **, IR *> m_save;
  for (auto &iter : relationmap) {
    type_to_fix.insert(iter.first);
    type_to_fix.insert(iter.second);
  }

  auto ir_list = cut_subquery(root, m_save);

  for (auto stmt : ir_list) {
    vector<IR *> ir_to_fix;
    collect_ir(stmt, type_to_fix, ir_to_fix);
    for (auto ii : ir_to_fix) {
      ordered_ir.push_back(ii);
    }
    cross_stmt_map(graph, ir_to_fix, cross_map);
    vector<IR *> v_top_table;
    toptable_map(graph, ir_to_fix, v_top_table);
    for (auto ir : ir_to_fix) {
      auto idtype = ir->id_type_;
      // graph[ir].empty();
      if (relationmap.find(idtype) == relationmap.end()) {
        continue;
      }

      auto curptr = ir;
      bool flag = false;
      while (true) {
        auto pptr = locate_parent(stmt, curptr);
        if (pptr == NULL) break;
        while (pptr->left_ == NULL || pptr->right_ == NULL) {
          curptr = pptr;
          pptr = locate_parent(stmt, curptr);
          if (pptr == NULL) {
            flag = true;
            break;
          }
        }
        if (flag) break;

        auto to_search_child = pptr->left_;
        if (pptr->left_ == curptr) {
          to_search_child = pptr->right_;
        }

        auto match_ir = search_mapped_ir(to_search_child, relationmap[idtype]);
        if (match_ir != NULL) {
          if (ir->type_ == kColumnName && ir->left_ != NULL) {
            if (v_top_table.size() > 0)
              match_ir = v_top_table[get_rand_int(v_top_table.size())];
            graph[match_ir].insert(ir->left_);
            if (ir->right_) {
              graph[match_ir].insert(ir->right_);
              ir->left_->id_type_ = id_table_name;
              ir->right_->id_type_ = id_column_name;
              ir->id_type_ = id_whatever;
            }
          } else
            graph[match_ir].insert(ir);
          break;
        }
        curptr = pptr;
      }
    }
  }

  fix_back(m_save);
  return graph;
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

  if (cur->type_ == kStatementList) {
    int size = left_lib[kStatementList].size();
    auto new_right = deep_copy(left_lib[kStatementList][get_rand_int(size)]);
    auto new_res = new IR(kStatementList, OPMID(";"), res, new_right);
    return new_res;
  }

  if (res->right_ == NULL && res->left_ != NULL) {
    auto left_type = res->left_->type_;
    auto left_lib_size = left_lib[left_type].size();
    if (left_lib_size != 0) {
      auto new_right =
          deep_copy(left_lib[left_type][get_rand_int(left_lib_size)]);
      res->right_ = new_right;
      return res;
    }
  } else if (res->right_ != NULL && res->left_ == NULL) {
    auto right_type = res->right_->type_;
    auto right_lib_size = right_lib[right_type].size();
    if (right_lib_size != 0) {
      auto new_left =
          deep_copy(right_lib[right_type][get_rand_int(right_lib_size)]);
      res->left_ = new_left;
      return res;
    }
  }

  int lib_size = ir_libary_2D_[res->type_].size();
  if (lib_size == 0) {
    deep_delete(res);
    return NULL;
  }

  auto save = res;
  res = deep_copy(ir_libary_2D_[res->type_][get_rand_int(lib_size)]);
  deep_delete(save);

  return res;
}

IR *Mutator::strategy_replace(IR *cur) {
  assert(cur);

  MUTATESTART

  DOLEFT
  res = deep_copy(cur);

  auto new_node = get_from_libary_2D(res->left_);

  if (new_node != NULL) {
    new_node = deep_copy(new_node);
    if (res->left_ != NULL) {
      new_node->id_type_ = res->left_->id_type_;
    }
  }
  if (res->left_ != NULL) deep_delete(res->left_);
  res->left_ = new_node;

  DORIGHT
  res = deep_copy(cur);

  auto new_node = get_from_libary_2D(res->right_);
  if (new_node != NULL) {
    new_node = deep_copy(new_node);
    if (res->right_ != NULL) {
      new_node->id_type_ = res->right_->id_type_;
    }
  }
  if (res->right_ != NULL) deep_delete(res->right_);
  res->right_ = new_node;

  DOBOTH
  res = deep_copy(cur);

  auto new_left = get_from_libary_2D(res->left_);
  auto new_right = get_from_libary_2D(res->right_);

  if (new_left != NULL) {
    new_left = deep_copy(new_left);
    if (res->left_ != NULL) {
      new_left->id_type_ = res->left_->id_type_;
    }
  }

  if (new_right != NULL) {
    new_right = deep_copy(new_right);
    if (res->right_ != NULL) {
      new_right->id_type_ = res->right_->id_type_;
    }
  }

  if (res->left_) deep_delete(res->left_);
  if (res->right_) deep_delete(res->right_);
  res->left_ = new_left;
  res->right_ = new_right;

  MUTATEEND

  return res;
}

bool Mutator::lucky_enough_to_be_mutated(unsigned int mutated_times) {
  if (get_rand_int(mutated_times + 1) < LUCKY_NUMBER) {
    return true;
  }
  return false;
}

IR *Mutator::get_from_libary_2D(IR *ir) {
  static IR *empty_str = new IR(kStringLiteral, "");

  if (!ir) return NULL;

  auto &i = ir_libary_2D_[ir->type_];
  if (i.size() == 0) return empty_str;
  return i[get_rand_int(i.size())];
}

IR *Mutator::get_from_libary_2D_type(IRTYPE type) {
  auto &i = ir_libary_2D_[type];
  if (i.size() == 0) return NULL;
  return i[get_rand_int(i.size())];
}

IR *Mutator::get_from_libary_3D(IR *ir) {
  NODETYPE left_type = kEmpty, right_type = kEmpty;
  if (ir->left_) {
    left_type = ir->left_->type_;
  }
  if (ir->right_) {
    right_type = ir->right_->type_;
  }
  auto &i = ir_libary_3D_[left_type][right_type];
  if (i.size() == 0) return new IR(kStringLiteral, "");
  return i[get_rand_int(i.size())];
}

string Mutator::get_a_string() {
  unsigned com_size = common_string_libary.size();
  unsigned lib_size = string_libary.size();
  unsigned double_lib_size = lib_size * 2;

  unsigned rand_int = get_rand_int(double_lib_size + com_size);
  if (rand_int < double_lib_size) {
    return string_libary[rand_int >> 1];
  } else {
    rand_int -= double_lib_size;
    return common_string_libary[rand_int];
  }
}

unsigned long Mutator::get_a_val() {
  if (value_libary.size() == 0) return 0xdeadbeef;
  return value_libary[get_rand_int(value_libary.size())];
}

unsigned long Mutator::get_library_size() {
  unsigned long res = 0;

  for (auto &i : ir_libary_2D_) {
    res += i.second.size();
  }

  for (auto &i : ir_libary_3D_) {
    for (auto &j : i.second) {
      res += j.second.size();
    }
  }

  for (auto &i : left_lib) {
    res += i.second.size();
  }

  for (auto &i : right_lib) {
    res += i.second.size();
  }

  return res;
}

#ifdef _NON_REPLACE_
void Mutator::add_to_library(IR *ir) {
#else
void Mutator::add_to_library_core(IR *ir) {
#endif
  NODETYPE p_type = ir->type_;
  unsigned long p_hash = hash(ir->to_string());
  if (ir_libary_2D_hash_[p_type].find(p_hash) !=
      ir_libary_2D_hash_[p_type].end()) {
    return;
  }
  IR *ir_copy = deep_copy(ir);
  add_to_library_core(ir_copy);
}

#ifdef _NON_REPLACE_
void Mutator::add_to_library_core(IR *ir) {
#else
void Mutator::add_to_library(IR *ir) {
#endif

  string p_str = ir->to_string();
  unsigned long p_hash = hash(p_str);
  NODETYPE p_type = ir->type_;
  NODETYPE left_type = kEmpty, right_type = kEmpty;

  // update library_2D
  if (ir_libary_2D_hash_[p_type].find(p_hash) !=
      ir_libary_2D_hash_[p_type].end()) {
    return;
  }

  ir_libary_2D_hash_[p_type].insert(p_hash);

#ifdef _NON_REPLACE_
  ir_libary_2D_[p_type].push_back(ir);
#else
  ir_libary_2D_[p_type].push_back(deep_copy(ir));
#endif

  if (ir->left_) {
    left_type = ir->left_->type_;
#ifdef _NON_REPLACE_
    add_to_library_core(ir->left_);
#else
    add_to_library(ir->left_);
#endif
  }
  if (ir->right_) {
    right_type = ir->right_->type_;
#ifdef _NON_REPLACE_
    add_to_library_core(ir->right_);
#else
    add_to_library(ir->right_);
#endif
  }

  // update right_lib, left_lib
  if (ir->right_ && ir->left_) {
#ifdef _NON_REPLACE_
    right_lib[right_type].push_back(ir->left_);
    left_lib[left_type].push_back(ir->right_);
#else
    right_lib[right_type].push_back(deep_copy(ir->left_));
    left_lib[left_type].push_back(deep_copy(ir->right_));
#endif
  }

  // update library_3D
  set<unsigned long> &hash_map = ir_libary_3D_hash_[left_type][right_type];
  if (hash_map.find(p_hash) != hash_map.end()) {
    return;
  }

  ir_libary_3D_hash_[left_type][right_type].insert(p_hash);

#ifdef _NON_REPLACE_
  ir_libary_3D_[left_type][right_type].push_back(ir);
#else
  ir_libary_3D_[left_type][right_type].push_back(deep_copy(ir));
#endif

  return;
}

/*
* You don't need to traverse the whole tree,
* you only need to add a single node input.
*/
#ifdef _NON_REPLACE_
void Mutator::add_to_library_no_traverse(IR *ir) {
#else
void Mutator::add_to_library_core_no_traverse(IR *ir) {
#endif
  NODETYPE p_type = ir->type_;
  unsigned long p_hash = hash(ir->to_string());
  if (ir_libary_2D_hash_[p_type].find(p_hash) !=
      ir_libary_2D_hash_[p_type].end()) {
    return;
  }
  if(ir_libary_2D_[p_type].size() >= NUMOFNT) return;
  IR *ir_copy = deep_copy(ir);
  add_to_library_core_no_traverse(ir_copy);
}

#ifdef _NON_REPLACE_
void Mutator::add_to_library_core_no_traverse(IR *ir) {
#else
void Mutator::add_to_library_no_traverse(IR *ir) {
#endif

  string p_str = ir->to_string();
  unsigned long p_hash = hash(p_str);
  NODETYPE p_type = ir->type_;
  NODETYPE left_type = kEmpty, right_type = kEmpty;

  // update library_2D
  if (ir_libary_2D_hash_[p_type].find(p_hash) !=
      ir_libary_2D_hash_[p_type].end()) {
    return;
  }

  ir_libary_2D_hash_[p_type].insert(p_hash);

#ifdef _NON_REPLACE_
  ir_libary_2D_[p_type].push_back(ir);
#else
  ir_libary_2D_[p_type].push_back(deep_copy(ir));
#endif

  // update right_lib, left_lib
  if (ir->right_ && ir->left_) {
#ifdef _NON_REPLACE_
    right_lib[right_type].push_back(ir->left_);
    left_lib[left_type].push_back(ir->right_);
#else
    right_lib[right_type].push_back(deep_copy(ir->left_));
    left_lib[left_type].push_back(deep_copy(ir->right_));
#endif
  }

  // update library_3D
  set<unsigned long> &hash_map = ir_libary_3D_hash_[left_type][right_type];
  if (hash_map.find(p_hash) != hash_map.end()) {
    return;
  }

  ir_libary_3D_hash_[left_type][right_type].insert(p_hash);

#ifdef _NON_REPLACE_
  ir_libary_3D_[left_type][right_type].push_back(ir);
#else
  ir_libary_3D_[left_type][right_type].push_back(deep_copy(ir));
#endif

  return;
}

unsigned long Mutator::hash(string sql) {
  return ducking_hash(sql.c_str(), sql.size());
}

unsigned long Mutator::hash(IR *root) { return this->hash(root->to_string()); }

void Mutator::debug(IR *root) {
  std::cout << get_string_by_type(root->type_) << std::endl;
  if (root->left_) debug(root->left_);
  if (root->right_) debug(root->right_);
}

Mutator::~Mutator() {
  std::cout << "HERE" << std::endl;
  // delete ir_libary_3D_
  for (auto &i : ir_libary_3D_) {
    for (auto &j : i.second) {
      for (auto &ir : j.second) {
        deep_delete(ir);
      }
    }
  }

  // delete ir_libary_2D_
  for (auto &i : ir_libary_2D_) {
    for (auto &ir : i.second) {
      deep_delete(ir);
    }
  }

  // delete left_lib
  for (auto &i : left_lib) {
    for (auto &ir : i.second) {
      deep_delete(ir);
    }
  }

  // delete right_lib
  for (auto &i : right_lib) {
    for (auto &ir : i.second) {
      deep_delete(ir);
    }
  }
}

void Mutator::fix_one(map<IR *, set<IR *>> &graph, IR *fixed_key,
                      set<IR *> &visited) {
  if (fixed_key->id_type_ == id_create_table_name) {
    string tablename = fixed_key->str_val_;
    auto &colums = m_tables[tablename];
    for (auto &val : graph[fixed_key]) {
      if (val->id_type_ == id_create_column_name) {
        string new_column = gen_id_name();
        colums.push_back(new_column);
        val->str_val_ = new_column;
        visited.insert(val);
      } else if (val->id_type_ == id_top_table_name) {
        val->str_val_ = tablename;
        visited.insert(val);
        fix_one(graph, val, visited);
      }
    }
  } else if (fixed_key->id_type_ == id_top_table_name) {
    string tablename = fixed_key->str_val_;
    auto &colums = m_tables[tablename];

    for (auto &val : graph[fixed_key]) {
      if (val->id_type_ == id_column_name) {
        val->str_val_ = vector_rand_ele(colums);
        visited.insert(val);
      } else if (val->id_type_ == id_table_name) {
        val->str_val_ = tablename;
        visited.insert(val);
      } else if (val->id_type_ == id_index_name) {
        string new_index = gen_id_name();
        val->str_val_ = new_index;
        m_tables[new_index] = m_tables[tablename];
        v_table_names.push_back(new_index);
      }
    }
  }
}

void Mutator::fix_graph(map<IR *, set<IR *>> &graph, IR *root,
                        vector<IR *> &ordered_ir) {
  set<IR *> visited;

  reset_database();
  for (auto ir : ordered_ir) {
    auto iter = make_pair(ir, graph[ir]);

    if (visited.find(iter.first) != visited.end()) {
      continue;
    }
    visited.insert(iter.first);
    if (iter.second.empty()) {
      if (iter.first->id_type_ == id_column_name) {
        string tablename = vector_rand_ele(v_table_names);
        auto &colums = m_tables[tablename];
        iter.first->str_val_ = vector_rand_ele(colums);
        continue;
      }
    }
    if (iter.first->id_type_ == id_create_table_name ||
        iter.first->id_type_ == id_top_table_name) {
      if (iter.first->id_type_ == id_create_table_name) {
        string new_table_name = gen_id_name();
        v_table_names.push_back(new_table_name);
        iter.first->str_val_ = new_table_name;
      } else {
        iter.first->str_val_ = vector_rand_ele(v_table_names);
      }
      fix_one(graph, iter.first, visited);
    }
  }
}

/* tranverse ir in the order: _right ==> root ==> left_ */
string Mutator::fix(IR *root) {
  string res;
  auto *right_ = root->right_, *left_ = root->left_;
  auto *op_ = root->op_;
  auto type_ = root->type_;
  auto str_val_ = root->str_val_;
  auto f_val_ = root->f_val_;
  auto int_val_ = root->int_val_;
  auto id_type_ = root->id_type_;

  string tmp_right;
  if (right_ != NULL) tmp_right = fix(right_);

  if (type_ == kIdentifier &&
      (id_type_ == id_database_name || id_type_ == id_schema_name)) {
    if (get_rand_int(2) == 1)
      return string("main");
    else
      return string("temp");
  }

  if (type_ == kCmdPragma) {
    string res = "PRAGMA ";
    int lib_size = cmds_.size();
    string &key = cmds_[get_rand_int(lib_size)];
    res += key;

    int value_size = m_cmd_value_lib_[key].size();
    string value = m_cmd_value_lib_[key][get_rand_int(value_size)];
    if (!value.compare("_int_")) {
      value = string("=") +
              to_string(value_libary[get_rand_int(value_libary.size())]);
    } else if (!value.compare("_empty_")) {
      value = "";
    } else if (!value.compare("_boolean_")) {
      if (get_rand_int(2) == 0)
        value = "=false";
      else
        value = "=true";
    } else {
      value = "=" + value;
    }
    if (!value.empty()) res += value + ";";
    return res;
  }

  if (type_ == kFilePath || type_ == kPrepareTargetQuery ||
      type_ == kOptOrderType || type_ == kColumnType || type_ == kSetType ||
      type_ == kOptJoinType || type_ == kOptDistinct || type_ == kNullLiteral)
    return str_val_;
  if (type_ == kStringLiteral) {
    auto s = string_libary[get_rand_int(string_libary.size())];
    return "'" + s + "'";
  }
  if (type_ == kIntLiteral)
    return std::to_string(value_libary[get_rand_int(value_libary.size())]);
  if (type_ == kFloatLiteral || type_ == kconst_float)
    return std::to_string(
        float(value_libary[get_rand_int(value_libary.size())]) + 0.1);
  if (type_ == kconst_str)
    return string_libary[get_rand_int(string_libary.size())];
  ;
  if (type_ == kconst_int)
    return std::to_string(value_libary[get_rand_int(value_libary.size())]);

  if (!str_val_.empty()) return str_val_;

  if (op_ != NULL) res += op_->prefix_ + " ";
  if (left_ != NULL) res += fix(left_) + " ";
  if (op_ != NULL) res += op_->middle_ + " ";
  if (right_ != NULL) res += tmp_right + " ";
  if (op_ != NULL) res += op_->suffix_;

  trim_string(res);
  return res;
}

unsigned int Mutator::calc_node(IR *root) {
  unsigned int res = 0;
  if (root->left_) res += calc_node(root->left_);
  if (root->right_) res += calc_node(root->right_);

  return res + 1;
}

string Mutator::extract_struct2(IR *root) {
  static int counter = 0;
  string res;
  auto *right_ = root->right_, *left_ = root->left_;
  auto *op_ = root->op_;
  auto type_ = root->type_;
  auto str_val_ = root->str_val_;

  if (type_ == kColumnName && str_val_ == "*") return str_val_;
  if (type_ == kOptOrderType || type_ == kNullLiteral || type_ == kColumnType ||
      type_ == kSetType || type_ == kOptJoinType || type_ == kOptDistinct)
    return str_val_;
  if (root->id_type_ != id_whatever && root->id_type_ != id_module_name) {
    return "x" + to_string(counter++);
  }
  if (type_ == kPrepareTargetQuery || type_ == kStringLiteral) {
    string str_val = str_val_;
    str_val.erase(std::remove(str_val.begin(), str_val.end(), '\''),
                  str_val.end());
    str_val.erase(std::remove(str_val.begin(), str_val.end(), '"'),
                  str_val.end());
    string magic_string = magic_string_generator(str_val);
    unsigned long h = hash(magic_string);
    if (string_libary_hash_.find(h) == string_libary_hash_.end()) {
      string_libary.push_back(magic_string);
      string_libary_hash_.insert(h);
    }
    return "'y'";
  }
  if (type_ == kIntLiteral) {
    value_libary.push_back(root->int_val_);
    return "10";
  }
  if (type_ == kFloatLiteral || type_ == kconst_float) {
    value_libary.push_back((unsigned long)root->f_val_);
    return "0.1";
  }
  if (type_ == kconst_int) {
    value_libary.push_back(root->int_val_);
    return "11";
  }
  if (type_ == kFilePath) return "'file_name'";

  if (!str_val_.empty()) return str_val_;
  if (op_ != NULL) res += op_->prefix_ + " ";
  if (left_ != NULL) res += extract_struct2(left_) + " ";
  if (op_ != NULL) res += op_->middle_ + " ";
  if (right_ != NULL) res += extract_struct2(right_) + " ";
  if (op_ != NULL) res += op_->suffix_;

  trim_string(res);
  return res;
}

string Mutator::extract_struct(IR *root) {
  static int counter = 0;
  string res;
  auto *right_ = root->right_, *left_ = root->left_;
  auto *op_ = root->op_;
  auto type_ = root->type_;
  auto str_val_ = root->str_val_;

  if (type_ == kColumnName && str_val_ == "*") return str_val_;
  if (type_ == kOptOrderType || type_ == kNullLiteral || type_ == kColumnType ||
      type_ == kSetType || type_ == kOptJoinType || type_ == kOptDistinct)
    return str_val_;
  if (root->id_type_ != id_whatever && root->id_type_ != id_module_name) {
    return "x";
  }
  if (type_ == kPrepareTargetQuery || type_ == kStringLiteral) {
    string str_val = str_val_;
    str_val.erase(std::remove(str_val.begin(), str_val.end(), '\''),
                  str_val.end());
    str_val.erase(std::remove(str_val.begin(), str_val.end(), '"'),
                  str_val.end());
    string magic_string = magic_string_generator(str_val);
    unsigned long h = hash(magic_string);
    if (string_libary_hash_.find(h) == string_libary_hash_.end()) {
      string_libary.push_back(magic_string);
      string_libary_hash_.insert(h);
    }
    return "'y'";
  }
  if (type_ == kIntLiteral) {
    value_libary.push_back(root->int_val_);
    return "10";
  }
  if (type_ == kFloatLiteral || type_ == kconst_float) {
    value_libary.push_back((unsigned long)root->f_val_);
    return "0.1";
  }
  if (type_ == kconst_int) {
    value_libary.push_back(root->int_val_);
    return "11";
  }
  if (type_ == kFilePath) return "'file_name'";

  if (!str_val_.empty()) return str_val_;
  if (op_ != NULL) res += op_->prefix_ + " ";
  if (left_ != NULL) res += extract_struct(left_) + " ";
  if (op_ != NULL) res += op_->middle_ + " ";
  if (right_ != NULL) res += extract_struct(right_) + " ";
  if (op_ != NULL) res += op_->suffix_;

  trim_string(res);
  return res;
}

void Mutator::add_new_table(IR *root, string &table_name) {
  if (root->left_ != NULL) add_new_table(root->left_, table_name);

  if (root->right_ != NULL) add_new_table(root->right_, table_name);

  // add to table_name_lib_
  if (root->type_ == kTableName) {
    if (root->operand_num_ == 1) {
      table_name = root->left_->str_val_;
    } else if (root->operand_num_ == 2) {
      table_name = root->left_->str_val_ + "." + root->right_->str_val_;
    }
  }

  // add to column_name_lib_
  if (root->type_ == kColumnDef) {
    auto tmp = root->left_;
    if (tmp->type_ == kIdentifier) {
      if (!table_name.empty() && !tmp->str_val_.empty())
        ;
      m_tables[table_name].push_back(tmp->str_val_);
      if (find(v_table_names.begin(), v_table_names.end(), table_name) !=
          v_table_names.end())
        v_table_names.push_back(table_name);
    }
  }
}

void Mutator::reset_database() {
  m_tables.clear();
  v_table_names.clear();
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
  auto fixed = validate(ir_root);
  deep_delete(ir_root);
  if (fixed.empty()) return 0;

  char *sfixed = (char *)malloc(fixed.size() + 1);
  memcpy(sfixed, fixed.c_str(), fixed.size());
  sfixed[fixed.size()] = 0;

  new_buf = sfixed;
  new_len = fixed.size();

  return 1;
}
