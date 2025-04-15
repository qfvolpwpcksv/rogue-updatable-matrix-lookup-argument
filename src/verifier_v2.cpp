#include "verifier_v2.hpp"

Verifier_v2::Verifier_v2(Setup* setup, int n_chunks)
{
    this->setup = setup;
    this->_n_chunks = n_chunks;
    this->_log_n_chunks = (int)ceil(log2(n_chunks));
    this->_chunk_size = setup->_max_row;
    this->_log_chunk_size = (int)ceil(log2(_chunk_size));
}

Verifier_v2::~Verifier_v2()
{
}

bool Verifier_v2::verify_row(const Kopis_com<G1>& table_com, int row_i, RowProof_v2* proof)
{
    // first verify the ipa proof
    bool ver_res = true;
    int chunk_i = row_i / _chunk_size;
    int row_i_in_chunk = row_i % _chunk_size;
    // prepare binary vec for chunk_i
    F* chunk_i_in_bits = new F[_log_n_chunks];
    int_to_Fvec(chunk_i_in_bits, chunk_i, _log_n_chunks);
    if (!setup->gipp->verify_proof_k(proof->ipa_proof, table_com.com, chunk_i_in_bits, _log_n_chunks, true))
    {
        cout << "MIPP_Proof_k verify fails" << endl;
        ver_res = false;
    }
    GT lhs;
    G1 chunk_com = proof->ipa_proof->z;
    millerLoop(lhs, chunk_com - proof->row_proof->row_com, setup->h2);
    GT rhs; 
    G2* h2row = new G2[_log_chunk_size];
    int row_i_level; 
    for (int level = 0; level < _log_chunk_size; level++)
    {
        row_i_level = (row_i_in_chunk >> (_log_chunk_size - level - 1)) & 1;
        if (row_i_level == 1)
        {
            h2row[level] = setup->h2tvec[level] - setup->h2; // h^{t_l} - h^1
        }
        else
        {
            h2row[level] = setup->h2tvec[level]; // h^{t_l}
        }
    }
    millerLoopVec(rhs, proof->row_proof->qs, h2row, _log_chunk_size);
    delete[] h2row;
    if (!pre_exp_GT_equal_check(lhs, rhs))
    {
        cout << "Row proof check fail" << endl;
        ver_res = false;
    }
    
    return ver_res;
}

bool Verifier_v2::verify_rows(const Kopis_com<G1>& table_com, MultiRowProof_v2*proof)
{
    bool ver_res = true;
    
    int row_n = proof->row_n;
    G1* idx_com = proof->idx_com;
    int log_size = (int)ceil(log2(row_n)); // here row_n is the number of query rows. not log of the entire rows. 
    
    GT * htmi_com = new GT[_log_chunk_size];
    for (int l = 0; l< _log_chunk_size; l++)
    {
        htmi_com[l] = setup->precom_logk_l_gj_htl[log_size][l] / my_loop(idx_com[l+_log_n_chunks], setup->h2);
    }
    if (!setup->gipp->verify_proof_batched_tipp(proof->q_batched_tipp_proof, proof->C_q, htmi_com, proof->rand_s, _log_chunk_size))
    {
        cout << "Batched TIPP proof check fail" << endl;
        ver_res = false;
    }
    delete[] htmi_com; 
    for (int l = 0; l<_log_chunk_size; l++)
    {
        if (!pre_exp_GT_equal_check(proof->q_batched_tipp_proof->z[l], proof->ip_qh[l]))
        {
            cout << "ip_qh["<<l<<"] check fail" << endl;
            ver_res = false;
        }
    }

    // check MIPP proof. 
    F s_sq = proof->rand_s * proof->rand_s;
    if (!setup->gipp->verify_proof_k(proof->cf_mipp_proof, proof->rows_kopis_com, &s_sq, F_ONE))
    {
        cout << "MIPP proof check fail" << endl;
        ver_res = false;
    }
    if (proof->cf_mipp_proof->z != proof->rows_com_rlc)
    {
        cout << "poly_t_rlc check fail" << endl;
        ver_res = false;
    }

    // check chunks mipp proof
    if (!setup->gipp->verify_proof(proof->chunks_mipp_proof, table_com.com, proof->chunk_ssq_com, F_ONE))
    {
        cout << "chunks mipp proof check fail" << endl;
        ver_res = false;
    }
    G1 table_cum_s = proof->chunks_mipp_proof->z;
    // check chunk_ssq_com. 

    GT lhs = my_loop(table_cum_s - proof->rows_com_rlc, setup->h2); 
    GT rhs = setup->GT_zero;
    GT tmp;
    for (int l = 0; l < _log_chunk_size; l++)
    {
        rhs *= proof->ip_qh[l];
    }
    
    if (!pre_exp_GT_equal_check(lhs, rhs))
    {
        cout << "combined check fail" << endl; 
        
        ver_res =false;
    }

    // 0/1 check
    
    G1* cons1_com = new G1[_log_n_chunks+_log_chunk_size];
    for (int l = 0; l < _log_n_chunks+_log_chunk_size; l++)
    {
        cons1_com[l] = setup->precom_logk_gj[log_size] - idx_com[l];
    }
    if (!setup->gipp->verify_proof_batched_ipa(proof->q_batched_ipa_proof, idx_com, cons1_com, proof->rand_s_i, _log_n_chunks+_log_chunk_size))
    {
        cout << "Batched IPA proof check fail" << endl;
        ver_res = false;
    }
    delete[] cons1_com;

    return ver_res;
}


bool Verifier_v2::verify_rows_mini(const Kopis_com<G1>&table_com, MiniMultiRowProof_v2*proof, int row_n, G1*idx_com)
{
    bool ver_res = true;
    int log_size = (int)ceil(log2(row_n)); // here row_n is the number of query rows. not log of the entire rows. 
    
    //check TIPP and MIPP proofs. 
    GT * htmi_com = new GT[_log_chunk_size];
    for (int l = 0; l< _log_chunk_size; l++)
    {
        htmi_com[l] = setup->precom_logk_l_gj_htl[log_size][l] / my_loop(idx_com[l], setup->h2);
    }
    if (!setup->gipp->verify_proof_batched_tipp(proof->q_batched_tipp_proof, proof->C_q, htmi_com, proof->rand_s, _log_chunk_size))
    {
        cout << "Batched TIPP proof check fail" << endl;
        ver_res = false;
    }
    delete[] htmi_com; 

    // check MIPP proof. 
    F s_sq = proof->rand_s * proof->rand_s;
    if (!setup->gipp->verify_proof_k(proof->cf_mipp_proof, proof->rows_kopis_com, &s_sq, F_ONE))
    {
        cout << "MIPP proof check fail" << endl;
        ver_res = false;
    }
    if (proof->cf_mipp_proof->z != proof->rows_com_rlc)
    {
        cout << "poly_t_rlc check fail" << endl;
        ver_res =false;
    }

    // check chunks mipp proof
    if (!setup->gipp->verify_proof(proof->chunks_mipp_proof, table_com.com, proof->chunk_ssq_com, F_ONE))
    {
        cout << "chunks mipp proof check fail" << endl;
        ver_res = false;
    }
    G1 table_cum_s = proof->chunks_mipp_proof->z;


    GT lhs = my_loop(table_cum_s - proof->rows_com_rlc, setup->h2); 
    GT rhs = setup->GT_zero;
    GT tmp;
    for (int l = 0; l < _log_chunk_size; l++)
    {
        rhs *= proof->ip_qh[l];
    }
    
    if (!pre_exp_GT_equal_check(lhs, rhs))
    {
        cout << "combined check fail" << endl; 
        
        ver_res = false;
    }
    return ver_res;
}


bool Verifier_v2::verify_update_rows_new(const Kopis_com<G1>& old_table_com, const Kopis_com<G1>& new_table_com, UpdateRowsProof_New_v2*proof)
{
    bool ver_res = true;
    // step 1: matrix lookup in old_table/new_table

    // step 1.1 idx col check

    // id check 
    // step 1.2 mini rows check
    if(!verify_rows_mini(old_table_com, proof->old_proof, proof->row_n, proof->idx_com + _log_n_chunks))
    {
        cout << "old table lookup check fail" << endl;
        ver_res = false;
    }
    if(!verify_rows_mini(new_table_com, proof->new_proof, proof->row_n, proof->idx_com + _log_n_chunks))
    {
        cout << "new table lookup check fail" << endl;
        ver_res = false;
    }
    // step 5: CP-SNARK
    
    // step 8
    if (!setup->gipp->verify_proof_k(proof->old_delta_r1_r2_open->ipa_proof, proof->old_delta_com, proof->r1, F_ONE, true))
    {
        cout << "old delta ipa proof check fail" << endl;
        ver_res = false;
    }
    if(!setup->logrowcol_kzg->verify(proof->old_delta_r1_r2_open->ipa_proof->z, proof->r1+_log_n_chunks, proof->old_delta_r1_r2_open->val, proof->old_delta_r1_r2_open->kzg_proof, _log_chunk_size + setup->_log_col))
    {
        cout << "y1 old val kzg check fail" << endl;
        ver_res = false;
    }
    if (!setup->gipp->verify_proof_k(proof->new_delta_r1_r2_open->ipa_proof, proof->new_delta_com, proof->r1, F_ONE, true))
    {
        cout << "new delta ipa proof check fail" << endl;
        ver_res = false;
    }
    if(!setup->logrowcol_kzg->verify(proof->new_delta_r1_r2_open->ipa_proof->z, proof->r1+_log_n_chunks, proof->new_delta_r1_r2_open->val, proof->new_delta_r1_r2_open->kzg_proof, _log_chunk_size + setup->_log_col))
    {
        cout << "y1 new val kzg check fail" << endl;
        ver_res = false;
    }

    // step 9: CP-SNARK
    return ver_res;
}


bool Verifier_v2::verify_update_rows_newnew(const Kopis_com<G1>& old_table_com, const Kopis_com<G1>& new_table_com, UpdateRowsProof_NewNew_v2*proof)
{
    bool ver_res = true;
    // step 1: matrix lookup in old_table/new_table

    // step 1.1 idx col check

    // id check 
    // step 1.2 mini rows check
    int row_n = proof->row_n;
    int log_size = (int)ceil(log2(row_n)); // here row_n is the number of query rows. not log of the entire rows. 
    F rand_s = proof->lookup_proof->rand_s;
    F rand_s_sq = rand_s * rand_s;
    
    //check TIPP and MIPP proofs. 
    GT * htmi_com = new GT[_log_chunk_size];
    for (int l = 0; l< _log_chunk_size; l++)
    {
        htmi_com[l] = setup->precom_logk_l_gj_htl[log_size][l] / my_loop(proof->idx_com[l+_log_n_chunks], setup->h2);
    }
    if (!setup->gipp->verify_proof_batched_tipp(proof->lookup_proof->q_batched_tipp_proof, proof->lookup_proof->C_q, htmi_com, rand_s, setup->_log_row))
    {
        cout << "Batched TIPP proof check fail" << endl;
        ver_res = false;
    }
    delete[] htmi_com; 

    // check MIPP proof. 
    GT tilde_row_kopis_com;
    GT::pow(tilde_row_kopis_com, proof->new_F_kopis_com->com, proof->rand_lookup);
    tilde_row_kopis_com = tilde_row_kopis_com * proof->old_F_kopis_com->com;
    if (!setup->gipp->verify_proof_k(proof->lookup_proof->cf_mipp_proof, tilde_row_kopis_com, &rand_s_sq, F_ONE))
    {
        cout << "MIPP proof check fail" << endl;
        ver_res = false;
    }
    if (proof->lookup_proof->cf_mipp_proof->z != proof->lookup_proof->rows_com_rlc)
    {
        cout << "poly_t_rlc check fail" << endl;
        ver_res =false;
    }

    // check chunks mipp proof
    GT tilde_table_kcom;
    GT::pow(tilde_table_kcom, new_table_com.com, proof->rand_lookup);
    tilde_table_kcom = tilde_table_kcom * old_table_com.com; 
    if (!setup->gipp->verify_proof(proof->lookup_proof->chunks_mipp_proof, tilde_table_kcom, proof->lookup_proof->chunk_ssq_com, F_ONE))
    {
        cout << "chunks mipp proof check fail" << endl;
        ver_res = false;
    }
    G1 tilde_table_cum_s = proof->lookup_proof->chunks_mipp_proof->z;
    // check chunk_ssq_com. 

    GT lhs = my_loop(tilde_table_cum_s - proof->lookup_proof->rows_com_rlc, setup->h2); 
    GT rhs = setup->GT_zero;
    GT tmp;
    for (int l = 0; l < setup->_log_row; l++)
    {
        rhs *= proof->lookup_proof->ip_qh[l];
    }
    
    if (!pre_exp_GT_equal_check(lhs, rhs))
    {
        cout << "combined check fail" << endl; 
        
        ver_res = false;
    }
    // step 5: CP-SNARK
    
    // step 8
    if (!setup->gipp->verify_proof_k(proof->old_delta_r1_r2_open->ipa_proof, proof->old_delta_com, proof->r1, F_ONE, true))
    {
        cout << "old delta ipa proof check fail" << endl;
        ver_res = false;
    }
    if(!setup->logrowcol_kzg->verify(proof->old_delta_r1_r2_open->ipa_proof->z, proof->r1+_log_n_chunks, proof->old_delta_r1_r2_open->val, proof->old_delta_r1_r2_open->kzg_proof, _log_chunk_size + setup->_log_col))
    {
        cout << "y1 old val kzg check fail" << endl;
        ver_res = false;
    }
    if (!setup->gipp->verify_proof_k(proof->new_delta_r1_r2_open->ipa_proof, proof->new_delta_com, proof->r1, F_ONE, true))
    {
        cout << "new delta ipa proof check fail" << endl;
        ver_res = false;
    }
    if(!setup->logrowcol_kzg->verify(proof->new_delta_r1_r2_open->ipa_proof->z, proof->r1+_log_n_chunks, proof->new_delta_r1_r2_open->val, proof->new_delta_r1_r2_open->kzg_proof, _log_chunk_size + setup->_log_col))
    {
        cout << "y1 new val kzg check fail" << endl;
        ver_res = false;
    }

    // step 9: CP-SNARK
    return ver_res;
}
