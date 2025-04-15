#pragma once
#include "config_pc.hpp"
#include "setup.hpp"
#include "kopis.hpp"

struct RowProof
{
    G1 row_com;
    G1 *qs;
    ~RowProof()
    {
        delete[] qs;
    }
};

struct RowAux
{
    int row_n;
    int log_max_row;
    int *rows;   // shallow copy from elsewhere
    G1 *idx_com; // will be given to update_rows_proof

    F **idx;    // will be given to update_rows_proof 
    G2 **hidx;  // will be given to update_rows_proof
    G2 **h_tmi; //
    ~RowAux()
    {
        for (int i = 0; i < log_max_row; i++)
        {
            delete[] h_tmi[i];
        }
        delete[] h_tmi;
    }
};

struct MiniMultiRowProof
{
    GT rows_kopis_com;
    G1 rows_com_rlc;
    GT *C_q;
    GT *ip_qh;
    BatchedTIPP_Proof *q_batched_tipp_proof;
    MIPP_Proof_k *cf_mipp_proof;
    int log_max_row;
    F rand_s;
    ~MiniMultiRowProof()
    {
        delete[] C_q;
        delete[] ip_qh;
        delete q_batched_tipp_proof;
        delete cf_mipp_proof;
    }
};

struct MultiRowProof
{
    GT rows_kopis_com; // C_F: <C_f, h_j = ck1>
    G1 rows_com_rlc;   // C_f ^ {s^j}
    int row_n;         // the number of rows.
    int log_max_row;   // 
    // GT* idx_com; // C_idx[l] = \prod_j e(g_j, h^{i_{j,l}})
    G1 *idx_com;
    GT *C_q; // C_pi[l] = \prod_j e(\pi_{ij, l}, h_j) com of pi
    GT *ip_qh; // e(pi, h^{t-i}) rlc
    BatchedTIPP_Proof *q_batched_tipp_proof;
    MIPP_Proof_k *cf_mipp_proof;
    F rand_s;
    F rand_s_i; // for proving that (1-i_{j,l})i_{j,l} s^j = 0
    BatchedIPA_Proof *q_batched_ipa_proof;
    ~MultiRowProof()
    {
        delete[] idx_com;
        delete[] C_q;
        delete[] ip_qh;
        delete q_batched_tipp_proof;
        delete cf_mipp_proof;
        delete q_batched_ipa_proof;
    }
};

struct UpdateRowsProof
{
    // index:
    int row_n;
    int log_max_row;
    G1 *idx_com; // GT com is e(idx_com, setup->h2)
    F **idx;
    // G2** hidx; // hidx_com[l][j] = h^{i_{j,l}}
    Kopis_com<G2> **idx_kcom; // hidx[l] = idx_kcom[l].row_coms

    Kopis_com<G1> *old_F_kopis_com;
    Kopis_com<G1> *new_F_kopis_com;
    MiniMultiRowProof *old_proof;
    MiniMultiRowProof *new_proof;

    G1 old_delta_com;
    G1 new_delta_com;

    Kopis_com<G2> *beta_kcom;
    F *r1; // log-k
    F *r2; // log-n

    Kopis_open_G2 *beta_r1_r2_open;

    TIPP_Proof *old_delta_tipp;
    TIPP_Proof *new_delta_tipp;
    ~UpdateRowsProof()
    {
        delete[] idx_com;
        for (int l = 0; l < log_max_row; l++)
        {
            delete[] idx[l];
            delete idx_kcom[l];
        }
        delete[] idx;
        delete[] idx_kcom;
        if (old_F_kopis_com != nullptr)
            delete old_F_kopis_com;
        if (new_F_kopis_com != nullptr)
            delete new_F_kopis_com;
        delete old_proof;
        delete new_proof;

        delete beta_kcom;
        delete[] r1;
        // delete[] r2;
        delete beta_r1_r2_open;
        delete old_delta_tipp;
        delete new_delta_tipp;
    }
};

struct UpdateRowsProof_New
{
    // index:

    int row_n;
    int log_max_row;
    G1 *idx_com; // GT com is e(idx_com, setup->h2)
    F **idx;
    // G2** hidx; // hidx_com[l][j] = h^{i_{j,l}}
    Kopis_com<G2> **idx_kcom; // hidx[l] = idx_kcom[l].row_coms

    Kopis_com<G1> *old_F_kopis_com;
    Kopis_com<G1> *new_F_kopis_com;
    MiniMultiRowProof *old_proof;
    MiniMultiRowProof *new_proof;
    G1 old_delta_com;
    G1 new_delta_com;
    F *r1; // log-row
    F *r2; // log-col // actually = r1 + log_row
    F y_old_delta;
    F y_new_delta;
    G1 *y_old_proof; // of size log_row + log_col
    G1 *y_new_proof;
    ~UpdateRowsProof_New()
    {
        delete[] idx_com;
        for (int l = 0; l < log_max_row; l++)
        {
            delete[] idx[l];
            delete idx_kcom[l];
        }
        delete[] idx;
        delete[] idx_kcom;

        delete old_F_kopis_com;
        delete new_F_kopis_com;
        delete old_proof;
        delete new_proof;
        delete[] r1;
        // delete[] r2;
        delete[] y_old_proof;
        delete[] y_new_proof;
    }
};

struct UpdateRowsProof_NewNew
{
    // index:

    int row_n;
    int log_max_row;
    G1 *idx_com; // GT com is e(idx_com, setup->h2)
    F **idx;
    // G2** hidx; // hidx_com[l][j] = h^{i_{j,l}}
    Kopis_com<G2> **idx_kcom; // hidx[l] = idx_kcom[l].row_coms
    // add other parts

    Kopis_com<G1> *old_F_kopis_com;
    Kopis_com<G1> *new_F_kopis_com;

    F rand_lookup; // F + rand_lookup * F' | T + rand_lookup * T'
    MiniMultiRowProof *lookup_proof;

    G1 old_delta_com;
    G1 new_delta_com;
    F *r1; // log-row
    F *r2; // log-col // actually = r1 + log_row
    F y_old_delta;
    F y_new_delta;
    G1 *y_old_proof; // of size log_row + log_col
    G1 *y_new_proof;
    ~UpdateRowsProof_NewNew()
    {
        delete[] idx_com;
        for (int l = 0; l < log_max_row; l++)
        {
            delete[] idx[l];
            delete idx_kcom[l];
        }
        delete[] idx;
        delete[] idx_kcom;

        delete old_F_kopis_com;
        delete new_F_kopis_com;
        delete lookup_proof;
        delete[] r1;
        // delete[] r2;
        delete[] y_old_proof;
        delete[] y_new_proof;
    }
};

class Prover
{
public:
    Prover(Setup *setup);
    ~Prover();

    void init(F **data, int row_size, int col_size, bool dummy = false);

    UpdateRowsProof *update_rows(int *rows, F **new_data, int row_n, bool dummy = false);
    UpdateRowsProof_New *update_rows_new(int *rows, F **new_data, int row_n, bool dummy = false);
    UpdateRowsProof_NewNew *update_rows_newnew(int *rows, F **new_data, int row_n, bool dummy = false);

    RowProof *prove_row(int row, bool dummy = false); // given a row, generate a proof for that row

    RowAux *generate_aux_for_rows(int *rows, int row_n);

    MiniMultiRowProof *_mini_prove_rows(RowAux *aux, Kopis_com<G1> *rows_kcom, bool dummy = false);
    MultiRowProof *prove_rows(int *rows, int row_n, G1 *sub_row_coms, bool dummy = false);

    G1 table_com;

    Setup *setup;
    void update_row(int row, F *data, int data_col, G1 *row_com = nullptr, bool dummy = false); // update table preprocessing. Can provide a precomputed row_com to avoid computing it again.
    G1 *row_coms;
    G1 *row_beta_coms;
    F **_data; // for convinience, every row appends zero to have length max_col
    G1 **quotients_trees;
};
