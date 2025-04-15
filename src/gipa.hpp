#pragma once

#include "config_pc.hpp"
#include "basic_utils.hpp"
#include <type_traits>


// ############## PART1: proof data structs ##############

struct MIPP_Proof
{
    G1 z;
    G1 final_x;
    F final_y;
    F r_c1;
    F r_c2;
    GT *cL;
    GT *cR;
    F *r_challenges;

    G2 final_ck1;
    G1 final_ck2;
    int log_size;

    F r_cha_ck1; 
    F r_cha_ck2;
    F ck1_val; 
    F ck2_val;
    G2 proof_ck1;
    G1 proof_ck2;

    int size_in_bytes()
    {
        int size_of_mipp = sizeof(G1) * 2 + sizeof(F) * 3 + sizeof(GT*)*2 + sizeof(F*) + sizeof(G2) + sizeof(G1) + sizeof(int) + sizeof(F)*4 + sizeof(G2) + sizeof(G1);
        return size_of_mipp + sizeof(GT) * log_size * 2 + sizeof(F) * log_size;
    }

    ~MIPP_Proof()
    {
        delete[] cL;
        delete[] cR;
        delete[] r_challenges;
    }
} ;

struct MIPP_Proof_k
{
    G1 z;
    G1 final_x;
    F r_c;
    GT *cL;
    GT *cR;
    F *r_challenges;

    G2 final_ck1;
    int log_size;

    F r_cha_ck1;  // z
    F ck1_val;    // f(z)
    G2 proof_ck1; // g*Q_z(tau)

    int size_in_bytes()
    {
        int size_of_mipp = sizeof(G1) * 2 + sizeof(F) + sizeof(GT*)*2 + sizeof(F*) + sizeof(G2) + sizeof(int) + sizeof(F)*2 + sizeof(G2);
        return size_of_mipp + sizeof(GT) * log_size * 2 + sizeof(F) * log_size;
    }
    ~MIPP_Proof_k()
    {
        delete[] cL;
        delete[] cR;
        delete[] r_challenges;
    }
};

int size_of_mipp_k(int row_n);

struct MIPP_Proof_k_G2
{
    G2 z;
    G2 final_x;
    F r_c;
    GT *cL;
    GT *cR;
    F *r_challenges;

    G1 final_ck1;
    int log_size;

    F r_cha_ck1;  // z
    F ck1_val;    // f(z)
    G1 proof_ck1; // g*Q_z(tau)

    int size_in_bytes()
    {
        int size_of_mipp = sizeof(G2) * 2 + sizeof(F) + sizeof(GT*)*2 + sizeof(F*) + sizeof(G1) + sizeof(int) + sizeof(F)*2 + sizeof(G1);
        return size_of_mipp + sizeof(GT) * log_size * 2 + sizeof(F) * log_size;
    }

    ~MIPP_Proof_k_G2()
    {
        delete[] cL;
        delete[] cR;
        delete[] r_challenges;
    }
} ;

struct IPA_Proof
{
    F z;
    F final_x;
    F final_y;
    G1 final_ck1;
    G1 final_ck2;
    int log_size;
    G1 *cL;
    G1 *cR;
    F r_c2;
    F r_cz;
    F *r_challenges; 

    F r_cha_ck1; // z
    F r_cha_ck2;
    F ck1_val; // f(z)
    F ck2_val;
    G1 proof_ck1; // g*Q_z(tau)
    G1 proof_ck2;

    int size_in_bytes()
    {
        int size_of_ipa = sizeof(F)*3 + sizeof(G1)*2+sizeof(int) + sizeof(G1*)*2+sizeof(F)*2 + sizeof(F*) + sizeof(F)*4 + sizeof(G1)*2;
        return size_of_ipa + sizeof(G1) * log_size * 2 + sizeof(F) * log_size;
    }
    ~IPA_Proof()
    {
        delete[] cL;
        delete[] cR;
        delete[] r_challenges;
    }
};

struct BatchedIPA_Proof
{
    int proof_num;
    F *rand_a; // rand_a[proof_num] to combine proof_num proofs.
    F*z; 
    F*final_x;
    F*final_y;
    G1 final_ck1;
    G1 final_ck2;
    int log_size;
    G1*cL;
    G1*cR;
    F r_c2;
    F r_cz;
    F* r_challenges; // r_challenges[log_size]
    F r_cha_ck1; // z
    F r_cha_ck2;
    F ck1_val; // f(z)
    F ck2_val;
    G1 proof_ck1; // g*Q_z(tau)
    G1 proof_ck2;

    int size_in_bytes()
    {
        int size_of_batched_proof = sizeof(int) + sizeof(F*)*4 + sizeof(G1)*2 + sizeof(int) + sizeof(G1*)*2 + sizeof(F)*2 + sizeof(F*) + sizeof(F)*4 + sizeof(G1)*2;
        return size_of_batched_proof + sizeof(F) * proof_num*4 + sizeof(G1) * log_size * 2 + sizeof(F) * log_size; 
    }


    ~BatchedIPA_Proof()
    {
        delete[] rand_a;
        delete[] z;
        delete[] final_x;
        delete[] final_y;

        delete[] cL;
        delete[] cR;
        delete[] r_challenges;
    }
};  

struct TIPP_Proof
{
    GT z;
    G1 final_x;
    G2 final_y;
    G2 final_ck1;
    G1 final_ck2;
    int log_size;
    GT *cL_x_coms;
    GT *cR_x_coms;
    GT *cL_y_coms;
    GT *cR_y_coms;
    GT *zLs;
    GT *zRs;
    F *r_challenges; 

    F r_cha_ck1; // z
    F r_cha_ck2;
    F ck1_val; // f(z)
    F ck2_val;
    G2 proof_ck1; // g*Q_z(tau)
    G1 proof_ck2;

    int size_in_bytes()
    {
        int size_of_tipp = sizeof(GT) + sizeof(G1) + sizeof(G2) +sizeof(G2) + sizeof(G1) + sizeof(int) + sizeof(GT*)*6 + sizeof(F*) + sizeof(F)*4 + sizeof(G2) + sizeof(G1);
        return size_of_tipp + sizeof(GT) * log_size * 6 + sizeof(F) * log_size;
    }

    ~TIPP_Proof()
    {
        delete[] cL_x_coms;
        delete[] cR_x_coms;
        delete[] cL_y_coms;
        delete[] cR_y_coms;
        delete[] zLs;
        delete[] zRs;
        delete[] r_challenges;
    }
};

struct BatchTIPP_Aux{
    GT* z; // nullptr if not provided. 
    GT*zL_0; 
    GT*zR_0;
};


struct BatchedTIPP_Proof{
    int proof_num; 
    F* rand_a; // rand_a[proof_num] to combine proof_num proofs. 

    GT* z; //  proof_num
    G1* final_x; // proof_num
    G2* final_y; // proof_num
    G2 final_ck1;
    G1 final_ck2; 
    int log_size;
    GT* cL_x_coms;
    GT* cR_x_coms;
    GT* cL_y_coms;
    GT* cR_y_coms;
    GT** zLs; // zLs[log_size][proof_num]
    GT** zRs; // zRs[log_size][proof_num]
    F* r_challenges; // r_challenges[log_size]

    F r_cha_ck1; // 
    F r_cha_ck2;
    F ck1_val; //
    F ck2_val;
    G2 proof_ck1; //
    G1 proof_ck2;

    int size_in_bytes()
    {
        int size_of_batched_proof = sizeof(int) + sizeof(F*) + sizeof(GT*) + sizeof(G1*) + sizeof(G2*) + sizeof(G2) + sizeof(G1) + sizeof(int) + sizeof(GT*)*4 + sizeof(GT**)*2 + sizeof(F*) + sizeof(F)*4 + sizeof(G2) + sizeof(G1);
        return size_of_batched_proof + sizeof(F) * proof_num + sizeof(GT) * proof_num + sizeof(G1) * proof_num + sizeof(G2) * proof_num + sizeof(GT) * log_size * 4 + ((sizeof(GT) * proof_num + sizeof(GT*)) * log_size) * 2 + sizeof(F) * log_size;
    }

    ~BatchedTIPP_Proof(){
        delete[] rand_a;
        delete[] z; 
        delete[] final_x;
        delete[] final_y;
        delete[] cL_x_coms;
        delete[] cR_x_coms;
        delete[] cL_y_coms;
        delete[] cR_y_coms;
        for (int i=0;i<log_size;i++){
            delete[] zLs[i];
            delete[] zRs[i];
        }
        delete[] zLs;
        delete[] zRs;
        delete[] r_challenges;
    }

    
};

class GIPP
{
public:
    GIPP();
    void setup(int max_size, const G1 *g1p = nullptr, const G2 *h2p = nullptr, bool dummy = false);
    ~GIPP();

    MIPP_Proof *generate_proof(G1 *x, F *y, F rlc, int size);
    MIPP_Proof_k *generate_proof_k(G1 *x, F *y_gen, F rlc, int size, bool y_is_beta = false); // y_is_beta: y_i = beta(y_gen, i) | otherwise, y_i = y_gen^i
    MIPP_Proof_k_G2 *generate_proof_k_G2(G2 *x, F *y_gen, F rlc, int size, bool y_is_beta = false);
    IPA_Proof *generate_proof_ipa(F *x, F *y, F rlc, int size);
    BatchedIPA_Proof* generate_proof_batched_ipa(F** x, F** y, F rlc, int size, int proof_num);
    TIPP_Proof *generate_proof_tipp(G1 *x, G2 *y, F rlc, int size, GT*z_precom=nullptr);
    BatchedTIPP_Proof* generate_proof_batched_tipp(G1** x, G2** y, F rlc, int size, int proof_num, BatchTIPP_Aux* aux=nullptr);

    void prove_single_round(MIPP_Proof *proof, G1 *x, F *y, G2 *ck1, G1 *ck2, G2 &h1_c1, G2 &h2_c2, int size, int round);
    void prove_single_round_k(MIPP_Proof_k *proof, G1 *x, F *y, G2 *ck1, F *ck2, G2 &h_c, int size, int round);
    void prove_single_round_k_G2(MIPP_Proof_k_G2 *proof, G2 *x, F *y, G1 *ck1, F *ck2, G1 &g_c, int size, int round);
    void prove_single_round_ipa(IPA_Proof *proof, F *x, F *y, G1 *ck1, G1 *ck2, F &r_c2, G1 &g1c, int size, int round);
    void prove_single_round_batched_ipa(BatchedIPA_Proof* proof, F** x, F** y, G1* ck1, G1* ck2, F& r_c2, G1& g1c, int size, int round, int proof_num);
    void prove_single_round_tipp(TIPP_Proof *proof, G1 *x, G2 *y, G2 *ck1, G1 *ck2, int size, int round);
    void prove_single_round_batched_tipp(BatchedTIPP_Proof* proof, G1** x, G2** y, G2* ck1, G1* ck2, int size, int round, int proof_num, BatchTIPP_Aux* aux=nullptr);

    bool verify_proof(MIPP_Proof *proof, GT x_com, G1 y_com, F rlc);
    bool verify_proof_k(MIPP_Proof_k *proof, GT x_com, F *y_gen, F rlc, bool y_is_beta = false);
    bool verify_proof_k_G2(MIPP_Proof_k_G2 *proof, GT x_com, F *y_gen, F rlc, bool y_is_beta = false); // y_is_beta: y_i = beta(y_gen, i) | otherwise, y_i = y_gen^i
    bool verify_proof_ipa(IPA_Proof *proof, G1 x_com, G1 y_com, F rlc);
    bool verify_proof_batched_ipa(BatchedIPA_Proof* proof, G1* x_com, G1* y_com, F rlc, int proof_num);
    bool verify_proof_tipp(TIPP_Proof *proof, GT x_com, GT y_com, F rlc);
    bool verify_proof_batched_tipp(BatchedTIPP_Proof* proof, GT* x_com, GT* y_com, F rlc, int proof_num);

    template <typename T1, typename T2>
    void prove_final_ck1_T1_ck2_T2(int log_size, F *r_cha_ck1, F *ck1_val, T1 *proof_ck1, F *r_cha_ck2, F *ck2_val, T2 *proof_ck2, F *r_challenges, F rlc_sq, bool ck1_enabled, bool ck2_enabled);

    int max_size;

    // common public parameter
    G1 g1;
    G2 h2;
    G2 mipp_h1, mipp_h2;
    G1 mipp_g1; // for IPA. raise F to G1.

    // prover key
    G1 *pk_g1; // g^{alpha^{i}} 0~2m-2
    G2 *pk_h2; // h^{beta^{i}}
    G1 *ck_g1; // g^{alpha^{2i}}
    G2 *ck_h2; // h^{beta^{2i}}

    // verifier key
    G1 vk_g_beta;  // g^{beta}
    G2 vk_h_alpha; // h^{alpha}

private:
    F _alpha; // for MIPP/TIPP
    F _beta;  // for MIPP/TIPP
    bool local_setup; 
};

template <typename T1, typename T2>
void GIPP::prove_final_ck1_T1_ck2_T2(int log_size, F *r_cha_ck1, F *ck1_val, T1 *proof_ck1, F *r_cha_ck2, F *ck2_val, T2 *proof_ck2, F *r_challenges, F rlc_sq, bool ck1_enabled, bool ck2_enabled)
{
    int size = 1 << log_size;
    int poly_size = 2 * size - 1;
    F *poly_ck1;
    F *poly_ck2;
    F temp, temp2;
    if (ck1_enabled)
        poly_ck1 = new F[poly_size];
    if (ck2_enabled)
        poly_ck2 = new F[poly_size];
    F rlc_tower = rlc_sq;
    // suppose i = i0 i1 ... i_{d-1}
    // poly_ck2[2*i] = r0^{i0} * r1^{i1} * ... * r_{d-1}^{i_{d-1}}
    // poly_ck1[2*i] = 1/poly_ck2[2*i]/rlc_sq^i
    // rlc_sq^i = rlc_sq^{i0 * 2^{d-1} + i1 * 2^{d-2} + ... + i_{d-1}}
    F* arr1 = new F[size];
    F* arr2 = new F[size];
    F *ri_curr = arr1;
    F *ri_other = arr2;

    F *temp_f_ptr;

    ri_curr[0] = F_ONE;
    ri_curr[1] = r_challenges[0];

    for (int l = 1; l < log_size; l++)
    {
        temp_f_ptr = ri_curr;
        ri_curr = ri_other;
        ri_other = temp_f_ptr;
        for (int i = 0; i < (1 << l); i++)
        {
            ri_curr[2 * i] = ri_other[i];
            ri_curr[2 * i + 1] = ri_other[i] * r_challenges[l];
        }
    }

    if (ck1_enabled)
    {
        F* rlc_sq_power = new F[size];
        s_powers(rlc_sq_power, rlc_sq, size);
       
        for (int i = 0; i < size; i++)
        {
            poly_ck1[2 * i] = 1 / (ri_curr[i] * rlc_sq_power[i]);
            if (i < size - 1)
                poly_ck1[2 * i + 1] = F_ZERO;
        }
        *r_cha_ck1 = F(rand());
        *ck1_val = uni_eval_poly(poly_ck1, poly_size, *r_cha_ck1);
        F *q_ck1 = new F[poly_size];
        uni_compute_quotient_poly(q_ck1, poly_ck1, poly_size, *r_cha_ck1);
        if (is_same<T1, G1>::value)
        {
            
            G1 temp_g1 = ip_F_G1(q_ck1, pk_g1, poly_size - 1);
            *proof_ck1 = *(T1 *)(void *)(&temp_g1);
        }
        else if (is_same<T1, G2>::value)
        {
            G2 temp_g2 = ip_F_G2(q_ck1, pk_h2, poly_size - 1);
            *proof_ck1 = *(T1 *)(void *)(&temp_g2);
        }
        else
        {
            cout << "prove_final_ck1_T1_ck2_T2: unknown type T1" << endl;
            exit(-1);
        }
        delete[] poly_ck1;
        delete[] q_ck1;
        delete[] rlc_sq_power;
    }
    if (ck2_enabled)
    {
        for (int i = 0; i < size; i++)
        {
            poly_ck2[2 * i] = ri_curr[i];
            if (i < size - 1)
                poly_ck2[2 * i + 1] = F_ZERO;
        }
        *r_cha_ck2 = F(rand());
        *ck2_val = uni_eval_poly(poly_ck2, poly_size, *r_cha_ck2);
        F* q_ck2 = new F[poly_size];
        uni_compute_quotient_poly(q_ck2, poly_ck2, poly_size, *r_cha_ck2);
        if (is_same<T2, G1>::value)
        {
            G1 temp_g1 = ip_F_G1(q_ck2, pk_g1, poly_size - 1);
            *proof_ck2 = *(T2 *)(void *)(&temp_g1);
        }
        else if (is_same<T2, G2>::value)
        {
            G2 temp_g2 = ip_F_G2(q_ck2, pk_h2, poly_size - 1);
            *proof_ck2 = *(T2 *)(void *)(&temp_g2);
        }
        else
        {
            cout << "prove_final_ck1_T1_ck2_T2: unknown type T2" << endl;
            exit(-1);
        }
        delete[] poly_ck2;
        delete[] q_ck2;
    }
    delete[] arr1;
    delete[] arr2;
}
void set_dummy_mipp_proof(MIPP_Proof *proof, int log_size, const G1&g1r, const G2&g2r, const GT&gtr, const F&fr);
void set_dummy_mipp_proof_k(MIPP_Proof_k *proof, int log_size, const G1&g1r, const G2&g2r, const GT&gtr, const F&fr);
void set_dummy_tipp_proof(TIPP_Proof *proof, int log_size, const G1&g1r, const G2&g2r, const GT&gtr, const F&fr);
void set_dummy_ipa_proof(IPA_Proof *proof, int log_size, const G1&g1r, const G2&g2r, const GT&gtr, const F&fr);
void set_dummy_batched_ipa_proof(BatchedIPA_Proof* proof, int proof_num, int log_size, const G1&g1r, const G2&g2r, const GT&gtr, const F&fr);
void set_dummy_batched_tipp_proof(BatchedTIPP_Proof* proof, int proof_num, int log_size, const G1&g1r, const G2&g2r, const GT&gtr, const F&fr);