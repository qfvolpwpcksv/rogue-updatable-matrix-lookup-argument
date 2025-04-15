#pragma once

#include "config_pc.hpp"
#include "math.h"
#include <chrono>

using namespace std::chrono;

double get_time(high_resolution_clock::time_point t1, high_resolution_clock::time_point t2);

// ############## PART1: basic F/G1/G2 and vector operations ##############
F non_zero_rand();
int swap_bits_order(int a, int size);
void int_to_Fvec(F *res, int a, int size);

F beta(F *x, int idx, int x_size);
void beta_fullvec(F *res, F *x, int log_size); // res[i] = beta(x, i)

bool pairing_equal_check(G1 &a1, G2 &a2, G1 &b1, G2 &b2);
bool pre_exp_GT_equal_check(GT &a, GT &b);

GT my_final_exp(GT a);
GT my_pairing(G1 a, G2 b);
GT my_loop(G1 a, G2 b);

void printGT(GT a);

string GT_to_str(GT a);

F cum_power(F s, int size);

GT prod(GT *arr, int size);

void G1vec_sub(G1 *res, G1 *a, G1 *b, int size); // res = a - b
void G1vec_add(G1 *res, G1 *a, G1 *b, int size); // res = a + b
void G2vec_sub(G2 *res, G2 *a, G2 *b, int size); // res = a - b
void Fvec_sub(F *res, F *a, F *b, int size);
void Fvec_add(F *res, F *a, F *b, int size);
void Fvec_G1scalar(G1 *res, F *a, G1 b, int size); // res = a*b
void Fvec_G2scalar(G2 *res, F *a, G2 b, int size); // res = a*b

template <typename G>
void G_mulcopy(G *res, const G &val, int size) // res = [val, val, ...]
{
    for (int i = 0; i < size; i++)
    {
        res[i] = val;
    }
}

GT ip_G1_G2(G1 *data, G2 *ck, int size);
G2 ip_F_G2(F *data, G2 *ck, int size);
G1 ip_F_G1(F *data, G1 *ck, int size);
GT ip_F_GT(F *data, GT *ck, int size);
F ip_F_F(F *data1, F *data2, int size);

template <typename T>
T ip_F_G(F *data, T *ck, int size)
{
    T res;
    if (is_same<T, G1>::value)
        res = ip_F_G1(data, (G1 *)(void *)ck, size);
    if (is_same<T, G2>::value)
        res = ip_F_G2(data, (G2 *)(void *)ck, size);
    return res;
}

template <typename T>
void mulVec(T &res, T *ck, F *data, int size)
{
    if (is_same<T, G1>::value)
        G1::mulVec(*(G1 *)(void *)(&res), (G1 *)(void *)ck, data, size);
    if (is_same<T, G2>::value)
        G2::mulVec(*(G2 *)(void *)(&res), (G2 *)(void *)ck, data, size);
}

void G1vec_s_power(G1 *res, G1 *a, F s, int size); // res = [a, a*s, a*s^2, ...]
void G2vec_s_power(G2 *res, G2 *a, F s, int size); // res = [a, a*s, a*s^2, ...]
void Fvec_s_power(F *res, F *a, F s, int size); // res = [a, a*s, a*s^2, ...]
void s_powers(F *res, F s, int size); // res = [1, s, s^2, ...]

inline F f_power(F s, int i) // s^i
{
    F res = F_ONE;
    for (int j = 0; j < i; j++)
    {
        res *= s;
    }
    return res;
}

// ############## PART2: univariate KZG operations ##############
// by default UniKZG uses G1 com.

// the univariate polynomial is represented as its coefficients, starting from the constant term. size-1 is the largest degree.
// evaluate a univariate polynomial at a point
F uni_eval_poly(F *poly, int size, F point);
void uni_compute_quotient_poly(F *res, F *poly, int size, F point);
