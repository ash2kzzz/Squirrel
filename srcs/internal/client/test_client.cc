#include <cassert>
#include <cstring>
#include <iostream>
#include <string>
#include <fstream>
#include <map>
#include <streambuf>
#include <algorithm>

#include "db.h"
#include "utils.h"
#include "client.h"
#include "yaml-cpp/yaml.h"

#define TEST_NUM 5000

int main(int argc, char **argv) {
  YAML::Node config = YAML::LoadFile(std::string(argv[1]));

  std::string db_name = config["db"].as<std::string>();
  // client::PostgreSQLClient *test_client = new client::PostgreSQLClient;
  client::DBClient *test_client = client::create_client(db_name, config);
  test_client->initialize(config);
  /*
  if (test_client.connect()) {
    std::cout << "Success!" << std::endl;
  } else {
    std::cout << "Failed!" << std::endl;
  }
  */
  auto *mutator = create_database(config);
  auto *sq = new SquirrelMutator(mutator);
  std::string input_path("/root/ob_input");
  int test_num;
  std::map<client::ExecutionStatus, int> cal;
  cal[client::kConnectFailed] = 0;
  cal[client::kExecuteError] = 0;
  cal[client::kServerCrash] = 0;
  cal[client::kNormal] = 0;
  cal[client::kTimeout] = 0;
  cal[client::kSyntaxError] = 0;
  cal[client::kSemanticError] = 0;
  std::vector<std::string> file_list =
      get_all_files_in_dir(input_path.c_str());
  for (auto &f : file_list) {
    auto file_path = input_path + "/" + f;
    std::ifstream input_file(file_path);
    std::string input((std::istreambuf_iterator<char>(input_file)),
                 std::istreambuf_iterator<char>());
    replace(input.begin(), input.end(), '\n', '');
    sq->database->mutate(input);
    if (sq->database->validated_test_cases_num() >= TEST_NUM)
      break;
  }
  test_num = sq->database->validated_test_cases_num();

  while (sq->database->has_mutated_test_cases()) {
    sq->current_input = sq->database->get_next_mutated_query();
    const char *query = sq->current_input.c_str();
    test_client->prepare_env();
    client::ExecutionStatus result = test_client->execute(query, strlen(query));
    cal[result]++;
    test_client->clean_up_env();
  }

  std::cout << "test num:" << test_num << "\n";
  std::cout << "kConnectFailed:" << cal[client::kConnectFailed] << "\n";
  std::cout << "kExecuteError:" << cal[client::kExecuteError] << "\n";
  std::cout << "kServerCrash:" << cal[client::kServerCrash] << "\n";
  std::cout << "kNormal:" << cal[client::kNormal] << "\n";
  std::cout << "kTimeout:" << cal[client::kTimeout] << "\n";
  std::cout << "kSyntaxError:" << cal[client::kSyntaxError] << "\n";
  std::cout << "kSemanticError:" << cal[client::kSemanticError] << "\n";

  return 0;
}
