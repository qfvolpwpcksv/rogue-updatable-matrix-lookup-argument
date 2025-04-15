#pragma once
#include "config_pc.hpp"
#include "setup.hpp"
#include "kopis.hpp"
#include "prover.hpp"


struct RowProof_v2{
    MIPP_Proof_k* ipa_proof; // MIPP proof of opening chunks_kcom at chunk_i
    // ipa_proof->z is the kzg com of chunk_i. Next check kzg proof
    RowProof* row_proof; 
    ~RowProof_v2()
    {
        delete row_proof;
        delete ipa_proof;
    }
};

struct RowAux_v2{
    int row_n;
    int log_chunk_size;
    int*rows; // shallow copy from elsewhere
    int*chunk_is; // owned
    int*row_is; // owned
    G1*idx_com; // will be given to update_rows_proof
    
    F**idx; // will be given to update_rows_proof 
    G2**hidx; // will be given to update_rows_proof
    G2**h_tmi; // 
    ~RowAux_v2()
    {
        delete[] chunk_is;
        delete[] row_is;
        for (int i = 0; i < log_chunk_size; i++)
        {
            delete[] h_tmi[i];
        }
        delete[] h_tmi;
    }
};

struct MiniMultiRowProof_v2{
    GT rows_kopis_com; 
    G1 rows_com_rlc; 
    GT* C_q;
    GT* ip_qh;
    BatchedTIPP_Proof* q_batched_tipp_proof;
    MIPP_Proof_k* cf_mipp_proof;
    G1 chunk_ssq_com; // com of s = [\sum_{j\in J_1} s^j, ..., \sum_{j\in J_k} s^j]
    MIPP_Proof* chunks_mipp_proof;
    int log_chunk_size;
    F rand_s;
    ~MiniMultiRowProof_v2()
    {
        delete[] C_q;
        delete[] ip_qh;
        delete q_batched_tipp_proof;
        delete cf_mipp_proof;
        delete chunks_mipp_proof;

    }
};

struct MultiRowProof_v2{
    GT rows_kopis_com; // C_F: <C_f, h_j = ck1> 
    G1 rows_com_rlc; // C_f ^ {s^j}
    int row_n; // the number of rows. 
    int log_chunk_size; // in order to delete all tipp proofs. 
    //GT* idx_com; // C_idx[l] = \prod_j e(g_j, h^{i_{j,l}})
    G1* idx_com;  
    GT* C_q; // C_pi[l] = \prod_j e(\pi_{ij, l}, h_j) com of pi
    // GT* C_h_tmi; // com of t_l - i_{j,l}
    GT* ip_qh; // e(pi, h^{t-i}) rlc
    BatchedTIPP_Proof* q_batched_tipp_proof;
    MIPP_Proof_k* cf_mipp_proof;
    G1 chunk_ssq_com; // com of s = [\sum_{j\in J_1} s^j, ..., \sum_{j\in J_k} s^j]
    MIPP_Proof* chunks_mipp_proof;
    F rand_s; 
    F rand_s_i; // for proving that (1-i_{j,l})i_{j,l} s^j = 0
    
    BatchedIPA_Proof* q_batched_ipa_proof;

    ~MultiRowProof_v2()
    {
        delete[] idx_com;
        delete[] C_q;
        delete[] ip_qh;
        delete q_batched_tipp_proof;
        delete cf_mipp_proof;
        delete chunks_mipp_proof;
        delete q_batched_ipa_proof;
    }

};


struct UpdateRowsProof_New_v2{
    // index: 
    
    int row_n;
    int log_chunk_size;
    G1*idx_com; // GT com is e(idx_com, setup->h2)
    F** idx; 
    // G2** hidx; // hidx_com[l][j] = h^{i_{j,l}}
    Kopis_com<G2>** idx_kcom; // hidx[l] = idx_kcom[l].row_coms
    // add other parts

    Kopis_com<G1>* old_F_kopis_com;
    Kopis_com<G1>* new_F_kopis_com;
    MiniMultiRowProof_v2* old_proof;
    MiniMultiRowProof_v2* new_proof;
    GT old_delta_com;
    GT new_delta_com;
    F* r1; // log-row
    F* r2; // log-col // actually = r1 + log_row
    Kopis_open* old_delta_r1_r2_open; // open proof of delta
    Kopis_open* new_delta_r1_r2_open; // open proof of delta'
    
    ~UpdateRowsProof_New_v2()
    {
        delete[] idx_com;
        for (int l = 0; l<log_chunk_size;l++)
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
        delete old_delta_r1_r2_open;
        delete new_delta_r1_r2_open;
    }
};

// NewNew: merge two lookup proofs into one
struct UpdateRowsProof_NewNew_v2{
    // index: 
    
    int row_n;
    int log_chunk_size;
    G1*idx_com; // GT com is e(idx_com, setup->h2)
    F** idx; 
    // G2** hidx; // hidx_com[l][j] = h^{i_{j,l}}
    Kopis_com<G2>** idx_kcom; // hidx[l] = idx_kcom[l].row_coms
    // add other parts

    Kopis_com<G1>* old_F_kopis_com;
    Kopis_com<G1>* new_F_kopis_com;
    F rand_lookup; // random value for lookup
    MiniMultiRowProof_v2* lookup_proof;
    GT old_delta_com;
    GT new_delta_com;
    F* r1; // log-row
    F* r2; // log-col // actually = r1 + log_row
    Kopis_open* old_delta_r1_r2_open; // open proof of delta
    Kopis_open* new_delta_r1_r2_open; // open proof of delta'
    
    ~UpdateRowsProof_NewNew_v2()
    {
        delete[] idx_com;
        for (int l = 0; l<log_chunk_size;l++)
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
        delete old_delta_r1_r2_open;
        delete new_delta_r1_r2_open;
    }
};

int size_of_lookup_proof(int _log_table_row, int _log_chunk_size, int _log_col, int row_n);
int size_of_mini_lookup_proof(int _log_table_row, int _log_chunk_size, int _log_col, int row_n); 
int size_of_update_proof(int _log_table_row, int _log_chunk_size, int _log_col, int row_n); 



class Prover_v2{
public: 
    Prover_v2(Setup* setup); 
    ~Prover_v2();
    
    void init(F**data, int row_size, int col_size, bool dummy=false);
    
    UpdateRowsProof_New_v2* update_rows_new(int*rows, F**new_data, int row_n, bool dummy=false);
    UpdateRowsProof_NewNew_v2* update_rows_newnew(int*rows, F**new_data, int row_n, bool dummy=false);
    
    RowProof_v2* prove_row(int row, bool dummy=false); // given a row, generate a proof for that row
    
    RowAux_v2* generate_aux_for_rows(int*rows, int row_n); 

    MiniMultiRowProof_v2* _mini_prove_rows(RowAux_v2*aux, Kopis_com<G1>* rows_kcom, bool dummy=false); 
    MultiRowProof_v2* prove_rows(int* rows, int row_n, G1*sub_row_coms, bool dummy=false);

    Setup* setup; 
    void update_row(int row, F*data, int data_col, G1*row_com=nullptr, bool dummy=false); // After a row is changed, update table preprocessing. 
    

    Prover** chunk_provers;
    Kopis_com<G1>* chunks_kcom;

    int _table_row; // max_row
    int _log_table_row; 
    int _n_chunks;
    int _log_n_chunks;
    int _chunk_size; // max_row / _n_chunks
    int _log_chunk_size; // log2(_chunk_size)
};
