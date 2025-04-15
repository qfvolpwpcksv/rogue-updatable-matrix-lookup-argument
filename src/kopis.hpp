#pragma once

#include "gipa.hpp"
#include "multi_kzg.hpp"

template <class T>
struct Kopis_com
{
    GT com;
    T *row_coms; // if size<4. set row_coms non-null. Otherwise, set row_coms null, use GT_com.
    int size;
    
    int size_in_bytes()
    {
        return sizeof(GT) + sizeof(int); 
    }
    Kopis_com()
    {
        row_coms = nullptr;
        size = 0;
    }
    Kopis_com(const Kopis_com& other)
    {
        com = other.com;
        size = other.size;
        row_coms = new T[size];
        memcpy(row_coms, other.row_coms, size * sizeof(T));
    }
    ~Kopis_com()
    {
        delete[] row_coms;
    }
};

struct Kopis_open
{
    F val; // f(r1, r2)
    // G1 f_r1_com; since ipa_proof contains the z, omit this in kopis open
    MIPP_Proof_k *ipa_proof; // (1) when size<4: ipa_proof=nullptr, (2) when size>=4 ipa_proof is single proof.
    G1 *kzg_proof;
    int col_dim;

    int size_in_bytes()
    {
        int size_of_kopis_open = sizeof(F) + sizeof(MIPP_Proof_k*) + sizeof(G1*) + sizeof(int);
        int _size = size_of_kopis_open + sizeof(G1)*col_dim;
        if (ipa_proof != nullptr)
        {
            _size += ipa_proof->size_in_bytes();
        }
        return _size;
    }
    ~Kopis_open()
    {
        if (ipa_proof != nullptr)
            delete ipa_proof;
        delete[] kzg_proof;
    }
};

int size_of_Kopis_open(int row_n, int col_dim);




struct Kopis_open_G2
{
    F val; // f(r1, r2)
    // G1 f_r1_com; since ipa_proof contains the z, omit this in kopis open
    MIPP_Proof_k_G2 *ipa_proof; // (1) when size<4: ipa_proof=nullptr, (2) when size>=4 ipa_proof is single proof.
    G2 *kzg_proof;
    int col_dim;
    int size_in_bytes()
    {
        int size_of_kopis_open_g2 = sizeof(F) + sizeof(MIPP_Proof_k_G2*) + sizeof(G2*) + sizeof(int);
        int _size = size_of_kopis_open_g2 + sizeof(G2)*col_dim;
        if (ipa_proof != nullptr)
            _size += ipa_proof->size_in_bytes();
        return _size;
    }
    ~Kopis_open_G2()
    {
        if (ipa_proof != nullptr)
            delete ipa_proof;
        delete[] kzg_proof;
    }
};

class Kopis
{
public:
    Kopis();
    void setup(int max_row, int max_col);
    void setup(GIPP *gipp, MultiKZG *kzg);
    ~Kopis();
    Kopis_com<G1> *commit(F **data, int row_n, int col_dim, int col_n = -1, G1 *row_coms = nullptr);                                            // can provide row_coms to save computation. will duplicate.
    void Kopisopen(Kopis_open *open_res, F **data, F *point_row, F *point_col, int row_n, int col_dim, int col_n = -1, G1 *row_coms = nullptr); // note that |point| = log_row+log_col
    void Kopisopen(Kopis_open *open_res, F **data, F *point_row, F *point_col, Kopis_com<G1> *k_com, int col_dim, int col_n = -1);              
    Kopis_open *Kopisopen(F **data, F *point_row, F *point_col, int row_n, int col_dim, int col_n = -1, G1 *row_coms = nullptr);               
    Kopis_open *Kopisopen(F **data, F *point_row, F *point_col, Kopis_com<G1> *k_com, int col_dim, int col_n = -1);                             
    bool verify(const Kopis_com<G1> &com, F *point_row, F *point_col, Kopis_open *open);

public:
    int _max_row;
    int _max_col;
    int _log_row; // log2(max_row)
    int _log_col; // log2(max_col)
    GIPP *gipp;   // for each different size use different gipp.
    MultiKZG *kzg;

    bool local_setup;
};

class Kopis_G2
{
public:
    Kopis_G2();
    void setup(int max_row, int max_col);
    void setup(GIPP *gipp, MultiKZG_G2 *kzg);
    ~Kopis_G2();
    Kopis_com<G2> *commit(F **data, int row_n, int col_dim, int col_n = -1, G2 *row_coms = nullptr); // can provide row_coms to save computation. will duplicate.

    Kopis_com<G2> *commit(F *data, int row_n, G2 *row_coms = nullptr); // special support for col=1. one dimension matrix. for idx_com

    void Kopisopen(Kopis_open_G2 *open_res, F **data, F *point_row, F *point_col, int row_n, int col_dim, int col_n = -1, G2 *row_coms = nullptr); // note that |point| = log_row+log_col

    void Kopisopen(Kopis_open_G2 *open_res, F **data, F *point_row, F *point_col, Kopis_com<G2> *k_com, int col_dim, int col_n = -1);
    Kopis_open_G2 *Kopisopen(F **data, F *point_row, F *point_col, int row_n, int col_dim, int col_n = -1, G2 *row_coms = nullptr);   
    Kopis_open_G2 *Kopisopen(F **data, F *point_row, F *point_col, Kopis_com<G2> *k_com, int col_dim, int col_n = -1); 

    Kopis_open_G2 *Kopisopen(F *data, F *point, Kopis_com<G2> *k_com); // special support for col=1. one dimension matrix. for idx_com
    bool verify(const Kopis_com<G2> &com, F *point_row, F *point_col, Kopis_open_G2 *open);

public:
    int _max_row;
    int _max_col;
    int _log_row; // log2(max_row)
    int _log_col; // log2(max_col)
    GIPP *gipp;   // for each different size use different gipp.
    MultiKZG_G2 *kzg;

    bool local_setup;
};