#include "basic_utils.hpp"


double get_time(high_resolution_clock::time_point t1, high_resolution_clock::time_point t2)
{
    return duration_cast<duration<double>>(t2 - t1).count();
}
// ############## PART1: basic F/G1/G2 and vector operations ##############



F non_zero_rand()
{
    F res;
    do
    {
        res = F(rand());
    } while (res == F_ZERO);
    return res;
}

int swap_bits_order(int a, int size)
{
    int res = 0;
    for (int i = 0; i < size; i++)
    {
        res = res << 1;
        res += a & 1;
        a = a >> 1;
    }
    return res;
}

void int_to_Fvec(F *res, int a, int size)
{
    for (int i = 0; i < size; i++)
    {
        res[i] = (a >> (size - 1 - i)) & 1;
    }
}

// beta O(size)
F beta(F *x, int idx, int x_size)
{
    F res = F_ONE;
    idx = swap_bits_order(idx, x_size);
    for (int i = 0; i < x_size; i++)
    {
        if (idx & 1)
        {
            res *= x[i];
        }
        else
        {
            res *= (F_ONE - x[i]);
        }
        idx = idx >> 1;
    }
    return res;
}

// complexity is O(size) = O(2^log_size)
void beta_fullvec(F *res, F *x, int log_size)
{
    if (log_size == 0)
    {
        res[0] = F_ONE;
        return;
    }
    F *tmp_arr = new F[1 << log_size];
    F *curr = res;
    F *other = tmp_arr;
    if ((log_size & 1) == 0)
    {
        curr = tmp_arr;
        other = res;
    }
    F *temp; // for swapping
    curr[0] = F_ONE - x[0];
    curr[1] = x[0];
    for (int i = 1; i < log_size; i++)
    {
        temp = curr;
        curr = other;
        other = temp;

        for (int j = 0; j < (1 << i); j++)
        {
            curr[2 * j] = other[j] * (F_ONE - x[i]);
            curr[2 * j + 1] = other[j] * x[i];
        }
    }
    delete[] tmp_arr;
}

bool pairing_equal_check(G1 &a1, G2 &a2, G1 &b1, G2 &b2) 
{
    GT e1, e2;
    millerLoop(e1, a1, a2);
    millerLoop(e2, b1, b2);
    return pre_exp_GT_equal_check(e1, e2);
}

bool pre_exp_GT_equal_check(GT &a, GT &b)
{
    try
    {
       return my_final_exp(a / b) == GT(1);
    }
    catch (...)
    {
        if (my_final_exp(a) == my_final_exp(b))
        {
            cout << "warning: 0/0 GT check" << endl;
            return true;
        }
        cout<<"exception in pairing_equal_check, very likely /0 error"<<endl;
        return false;
    }
}

GT my_final_exp(GT a)
{
    GT res;
    finalExp(res, a);
    return res;
}

GT my_pairing(G1 a, G2 b)
{
    GT res;
    millerLoop(res, a, b);
    finalExp(res, res);
    return res;
}

GT my_loop(G1 a, G2 b)
{
    GT res;
    millerLoop(res, a, b);
    return res;
}

void printGT(GT a)
{
    cout << GT_to_str(a);
}

string GT_to_str(GT a)
{
    return a.serializeToHexStr().substr(0, 16);
}

F cum_power(F s, int size)
{
    F res = F_ONE;
    F s_power = s;
    int log_size = int(ceil(log2(size)));
    for (int i = 0; i < log_size; i++)
    {
        res *= (F_ONE + s_power);
        s_power *= s_power;
    }
    return res;
}

GT prod(GT *arr, int size)
{
    GT res = arr[0];
    for (int i = 1; i < size; i++)
    {
        res *= arr[i];
    }
    return res;
}

void G1vec_sub(G1 *res, G1 *a, G1 *b, int size)
{
    for (int i = 0; i < size; i++)
    {
        res[i] = a[i] - b[i];
    }
}

void G1vec_add(G1 *res, G1 *a, G1 *b, int size)
{
    for (int i = 0; i < size; i++)
    {
        res[i] = a[i] + b[i];
    }
}

void G2vec_sub(G2 *res, G2 *a, G2 *b, int size)
{
    for (int i = 0; i < size; i++)
    {
        res[i] = a[i] - b[i];
    }
}

void Fvec_sub(F *res, F *a, F *b, int size)
{
    for (int i = 0; i < size; i++)
    {
        res[i] = a[i] - b[i];
    }
}

void Fvec_add(F *res, F *a, F *b, int size)
{
    for (int i = 0; i < size; i++)
    {
        res[i] = a[i] + b[i];
    }
}

void Fvec_G1scalar(G1 *res, F *a, G1 b, int size)
{
    for (int i = 0; i < size; i++)
    {
        res[i] = b * a[i];
    }
}

void Fvec_G2scalar(G2 *res, F *a, G2 b, int size)
{
    for (int i = 0; i < size; i++)
    {
        res[i] = b * a[i];
    }
}

GT ip_G1_G2(G1 *data, G2 *ck, int size)
{
    GT res;
    mcl::bls12::millerLoopVec(res, data, ck, size);
    return res;
}

G2 ip_F_G2(F *data, G2 *ck, int size)
{
    G2 res;
    G2::mulVec(res, ck, data, size);
    return res;
}

G1 ip_F_G1(F *data, G1 *ck, int size)
{
    G1 res;
    G1::mulVec(res, ck, data, size);
    return res;
}

GT ip_F_GT(F *data, GT *ck, int size)
{
    GT res = GT(1);
    GT tmp_res;
    for (int i = 0; i < size; i++)
    {
        GT::pow(tmp_res, ck[i], data[i]);
        res *= tmp_res;
    }
    return res;
}

F ip_F_F(F *data1, F *data2, int size)
{
    F res = F_ZERO;
    for (int i = 0; i < size; i++)
    {
        res += data1[i] * data2[i];
    }
    return res;
}

void G1vec_s_power(G1 *res, G1 *a, F s, int size)
{
    F s_power = F_ONE;
    for (int i = 0; i < size; i++)
    {
        res[i] = a[i] * s_power;
        s_power *= s;
    }
}

void G2vec_s_power(G2 *res, G2 *a, F s, int size)
{
    F s_power = F_ONE;
    for (int i = 0; i < size; i++)
    {
        res[i] = a[i] * s_power;
        s_power *= s;
    }
}

void Fvec_s_power(F *res, F *a, F s, int size)
{
    F s_power = F_ONE;
    for (int i = 0; i < size; i++)
    {
        res[i] = a[i] * s_power;
        s_power *= s;
    }
}

void s_powers(F *res, F s, int size)
{
    res[0] = F_ONE;
    for (int i = 1; i < size; i++)
    {
        res[i] = res[i - 1] * s;
    }
}

// ############## PART2: univariate kzg operations ##############

F uni_eval_poly(F *poly, int size, F point)
{
    F res;
    res = poly[size - 1];
    for (int i = size - 2; i >= 0; i--)
    {
        res = res * point + poly[i];
    }

    return res;
}

void uni_compute_quotient_poly(F *res, F *poly, int size, F point)
{
    res[size - 2] = poly[size - 1];
    for (int i = size - 3; i >= 0; i--)
    {
        res[i] = res[i + 1] * point + poly[i + 1];
    }
}
