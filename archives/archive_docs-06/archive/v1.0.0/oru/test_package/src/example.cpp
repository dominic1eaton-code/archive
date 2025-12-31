#include "oru.h"
#include <vector>
#include <string>

int main() {
    oru();

    std::vector<std::string> vec;
    vec.push_back("test_package");

    oru_print_vector(vec);
}
