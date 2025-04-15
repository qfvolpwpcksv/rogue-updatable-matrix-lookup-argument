#include "ec.hpp"
#include <iostream>
F a, B; 

void elliptic_curves_init() {
    a.setByCSPRNG();
    B.setByCSPRNG();

    cout<< "a : "<< a.getStr(16) << endl;
    cout << "b : " << B.getStr(16) << endl; 
}