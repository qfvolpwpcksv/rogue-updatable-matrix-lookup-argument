#include "verifier.hpp"

Verifier::Verifier(Setup *setup)
{
    this->setup = setup;
}

Verifier::~Verifier()
{
}

bool Verifier::verify_row(const G1 &table_com, int row_i, RowProof *proof)
{

    GT lhs;
    millerLoop(lhs, table_com - proof->row_com, setup->h2);
    GT rhs;
    G2 *h2row = new G2[setup->_log_row];
    int row_i_level;
    for (int level = 0; level < setup->_log_row; level++)
    {
        row_i_level = (row_i >> (setup->_log_row - level - 1)) & 1;
        if (row_i_level == 1)
        {
            h2row[level] = setup->h2tvec[level] - setup->h2;
        }
        else
        {
            h2row[level] = setup->h2tvec[level];
        }
    }
    millerLoopVec(rhs, proof->qs, h2row, setup->_log_row);
    delete[] h2row;
    return pre_exp_GT_equal_check(lhs, rhs);
}

bool Verifier::verify_rows(const G1 &table_com, MultiRowProof *proof)
{
    bool ver_res = true;
    // Directly available data: (1) C_T (com of full table), (2) C_idx (com of idx), (3) C_pi[l], (com of quotients at selected rows), (4) s (random rlc)

    // Precompute (does not depend on idx and table contents): \prod_k e(g_j, h^{t_l}). Only depending on k (the number of selected rows, can be quite regular), and t (determined by the setup).

    // Based on the above data, V should compute the following: (1)
    int row_n = proof->row_n;
    G1 *idx_com = proof->idx_com;
    int log_size = (int)ceil(log2(row_n));                         // here row_n is the number of query rows. not log of the entire rows.
    F cum_sum_s = cum_power(proof->rand_s * proof->rand_s, row_n); // (1+s) (1+s^2) (1+s^4) ... (1+s^{k/2}) = 1 + s + s^2 + ... + s^{k-1}
    G1 table_cum_s = table_com * cum_sum_s;
    // check TIPP and MIPP proofs.

    GT *htmi_com = new GT[setup->_log_row];
    for (int l = 0; l < setup->_log_row; l++)
    {
        htmi_com[l] = setup->precom_logk_l_gj_htl[log_size][l] / my_loop(idx_com[l], setup->h2);
    }
    if (!setup->gipp->verify_proof_batched_tipp(proof->q_batched_tipp_proof, proof->C_q, htmi_com, proof->rand_s, setup->_log_row))
    {
        cout << "Batched TIPP proof check fail" << endl;
        ver_res = false;
    }
    delete[] htmi_com;
    for (int l = 0; l < setup->_log_row; l++)
    {
        if (!pre_exp_GT_equal_check(proof->q_batched_tipp_proof->z[l], proof->ip_qh[l]))
        {
            cout << "ip_qh[" << l << "] check fail" << endl;
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

    GT lhs = my_loop(table_cum_s - proof->rows_com_rlc, setup->h2);
    GT rhs = setup->GT_zero;
    GT tmp;
    for (int l = 0; l < setup->_log_row; l++)
    {
        rhs *= proof->ip_qh[l];
    }

    if (!pre_exp_GT_equal_check(lhs, rhs))
    {
        cout << "combined check fail" << endl;

        ver_res = false;
    }

    // 0/1 check
    G1 *cons1_com = new G1[setup->_log_row];
    for (int l = 0; l < setup->_log_row; l++)
    {
        cons1_com[l] = setup->precom_logk_gj[log_size] - idx_com[l];
    }
    if (!setup->gipp->verify_proof_batched_ipa(proof->q_batched_ipa_proof, idx_com, cons1_com, proof->rand_s_i, setup->_log_row))
    {
        cout << "Batched IPA proof check fail" << endl;
        ver_res = false;
    }
    delete[] cons1_com;

    return ver_res;
}

bool Verifier::verify_rows_mini(const G1 &table_com, MiniMultiRowProof *proof, int row_n, G1 *idx_com)
{
    bool ver_res = true;
    int log_size = (int)ceil(log2(row_n));                         // here row_n is the number of query rows. not log of the entire rows.
    F cum_sum_s = cum_power(proof->rand_s * proof->rand_s, row_n); // (1+s) (1+s^2) (1+s^4) ... (1+s^{k/2}) = 1 + s + s^2 + ... + s^{k-1}
    G1 table_cum_s = table_com * cum_sum_s;
    // check TIPP and MIPP proofs.
    GT *htmi_com = new GT[setup->_log_row];
    for (int l = 0; l < setup->_log_row; l++)
    {
        htmi_com[l] = setup->precom_logk_l_gj_htl[log_size][l] / my_loop(idx_com[l], setup->h2);
    }
    if (!setup->gipp->verify_proof_batched_tipp(proof->q_batched_tipp_proof, proof->C_q, htmi_com, proof->rand_s, setup->_log_row))
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
        ver_res = false;
    }

    GT lhs = my_loop(table_cum_s - proof->rows_com_rlc, setup->h2);
    GT rhs = setup->GT_zero;
    GT tmp;
    for (int l = 0; l < setup->_log_row; l++)
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

bool Verifier::verify_update_rows(const G1 &old_table_com, const G1 &new_table_com, UpdateRowsProof *proof)
{
    bool ver_res = true;
    // step 1: matrix lookup in old_table/new_table

    if (!verify_rows_mini(old_table_com, proof->old_proof, proof->row_n, proof->idx_com))
    {
        cout << "old table lookup check fail" << endl;
        ver_res = false;
    }
    if (!verify_rows_mini(new_table_com, proof->new_proof, proof->row_n, proof->idx_com))
    {
        cout << "new table lookup check fail" << endl;
        ver_res = false;
    }

    // check the delta_tipp proofs
    if (!setup->gipp->verify_proof_tipp(proof->old_delta_tipp, proof->old_proof->rows_kopis_com, proof->beta_kcom->com, F_ONE))
    {
        cout << "old delta tipp check fail" << endl;
        ver_res = false;
        GT old_delta_com_h = my_loop(proof->old_delta_com, setup->h2);
        if (!pre_exp_GT_equal_check(proof->old_delta_tipp->z, old_delta_com_h))
        {
            cout << "old delta com does not match TIPP z" << endl;
            ver_res = false;
        }
    }
    if (!setup->gipp->verify_proof_tipp(proof->new_delta_tipp, proof->new_proof->rows_kopis_com, proof->beta_kcom->com, F_ONE))
    {
        cout << "new delta tipp check fail" << endl;
        ver_res = false;
        GT new_delta_com_h = my_loop(proof->new_delta_com, setup->h2);
        if (!pre_exp_GT_equal_check(proof->new_delta_tipp->z, new_delta_com_h))
        {
            cout << "new delta com does not match TIPP z" << endl;
            ver_res = false;
        }
    }

    // check CT C_delta
    if (new_table_com != old_table_com + proof->new_delta_com - proof->old_delta_com)
    {
        cout << "CT C_delta check fail" << endl;
        ver_res = false;
    }

    // the kzg check: e(g, h^{f}) = \prod_l e(q, h^{t-r2})
    if (!setup->kopis_g2->verify(*proof->beta_kcom, proof->r1, proof->r2, proof->beta_r1_r2_open))
    {
        cout << "old F kzg check fail" << endl;
        ver_res = false;
    }
    return ver_res;
}

bool Verifier::verify_update_rows_new(const G1 &old_table_com, const G1 &new_table_com, UpdateRowsProof_New *proof)
{
    bool ver_res = true;
    // step 1: matrix lookup in old_table/new_table

    // step 1.1 idx col check

    // id check
    // step 1.2 mini rows check
    if (!verify_rows_mini(old_table_com, proof->old_proof, proof->row_n, proof->idx_com))
    {
        cout << "old table lookup check fail" << endl;
        ver_res = false;
    }
    if (!verify_rows_mini(new_table_com, proof->new_proof, proof->row_n, proof->idx_com))
    {
        cout << "new table lookup check fail" << endl;
        ver_res = false;
    }
    // step 5: CP-SNARK

    // step 8
    if (!setup->logrowcol_kzg->verify(proof->old_delta_com, proof->r1, proof->y_old_delta, proof->y_old_proof, setup->_log_row + setup->_log_col))
    {
        cout << "y1 old val kzg check fail" << endl;
        ver_res = false;
    }
    if (!setup->logrowcol_kzg->verify(proof->new_delta_com, proof->r1, proof->y_new_delta, proof->y_new_proof, setup->_log_row + setup->_log_col))
    {
        cout << "y1 new val kzg check fail" << endl;
        ver_res = false;
    }

    // step 9: CP-SNARK
    return ver_res;
}

bool Verifier::verify_update_rows_newnew(const G1 &old_table_com, const G1 &new_table_com, UpdateRowsProof_NewNew *proof)
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
    F cum_sum_s = cum_power(rand_s_sq, row_n); // (1+s) (1+s^2) (1+s^4) ... (1+s^{k/2}) = 1 + s + s^2 + ... + s^{k-1}
    G1 tilde_table_cum_s = (old_table_com + new_table_com * proof->rand_lookup) * cum_sum_s;
    // check TIPP and MIPP proofs.
    GT *htmi_com = new GT[setup->_log_row];
    for (int l = 0; l < setup->_log_row; l++)
    {
        htmi_com[l] = setup->precom_logk_l_gj_htl[log_size][l] / my_loop(proof->idx_com[l], setup->h2);
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
        ver_res = false;
    }

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
    if (!setup->logrowcol_kzg->verify(proof->old_delta_com, proof->r1, proof->y_old_delta, proof->y_old_proof, setup->_log_row + setup->_log_col))
    {
        cout << "y1 old val kzg check fail" << endl;
        ver_res = false;
    }
    if (!setup->logrowcol_kzg->verify(proof->new_delta_com, proof->r1, proof->y_new_delta, proof->y_new_proof, setup->_log_row + setup->_log_col))
    {
        cout << "y1 new val kzg check fail" << endl;
        ver_res = false;
    }

    // step 9: CP-SNARK
    return ver_res;
}
