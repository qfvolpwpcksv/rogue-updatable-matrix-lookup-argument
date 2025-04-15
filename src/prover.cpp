#include "prover.hpp"

Prover::Prover(Setup *setup)
{
    this->setup = setup;
}

Prover::~Prover()
{
    delete[] row_coms;
    delete[] row_beta_coms;
    for (int i = 0; i < setup->_max_row; i++)
        delete[] _data[i];
    delete[] _data;
    for (int level = 0; level < setup->_log_row; level++)
    {
        delete[] quotients_trees[level];
    }
    delete[] quotients_trees;
}

void Prover::init(F **data, int row_size, int col_size, bool dummy)
{
    this->row_coms = new G1[setup->_max_row];
    this->row_beta_coms = new G1[setup->_max_row];
    this->table_com = setup->G1_zero;
    this->_data = new F *[setup->_max_row];

    // initialize quotients_trees;
    this->quotients_trees = new G1 *[setup->_log_row];

    for (int level = 0; level < setup->_log_row; level++)
    {
        quotients_trees[level] = new G1[1 << level];
        if (dummy)
        {
            for (int j = 0; j < (1 << level); j++)
            {
                quotients_trees[level][j] = setup->g1;
            }
        }
        else
        {
            for (int j = 0; j < (1 << level); j++)
            {
                quotients_trees[level][j] = setup->G1_zero;
            }
        }
    }

    if (dummy)
        table_com = setup->g1;

    G1 *quotients_i = new G1[setup->_log_row];
    for (int row_i = 0; row_i < row_size; row_i++)
    {
        this->_data[row_i] = new F[setup->_max_col];
        if (dummy)
        {
            for (int col_i = 0; col_i < setup->_max_col; col_i++)
            {
                this->_data[row_i][col_i] = setup->fr;
                row_coms[row_i] = setup->g1;
                row_beta_coms[row_i] = setup->g1;
            }
            continue;
        }
        memcpy(this->_data[row_i], data[row_i], col_size * sizeof(F));
        for (int col_i = col_size; col_i < setup->_max_col; col_i++)
        {
            this->_data[row_i][col_i] = F_ZERO;
        }

        row_coms[row_i] = setup->logcol_kzg->commit(data[row_i], setup->_log_col, col_size);
        row_beta_coms[row_i] = multi_beta_rowi_f_T(data[row_i], setup->g1tvec_tower_all[0], row_i, setup->_log_col, col_size);
        table_com += row_beta_coms[row_i];

        // compute quotients;
        multi_hyper_of_f_as_rowi(quotients_i, data[row_i], row_i, setup->_log_row, setup->_log_col, setup->g1tvec_tower_all, &row_coms[row_i], col_size);

        for (int level = 0; level < setup->_log_row; level++)
        {
            int block = row_i >> (setup->_log_row - level);
            quotients_trees[level][block] += quotients_i[level];
        }
    }
    for (int row_i = row_size; row_i < setup->_max_row; row_i++)
    {
        this->_data[row_i] = new F[setup->_max_col];
        if (dummy)
            continue;
        for (int col_i = 0; col_i < setup->_max_col; col_i++)
        {
            this->_data[row_i][col_i] = F_ZERO;
        }
        row_coms[row_i] = setup->G1_zero;
        row_beta_coms[row_i] = setup->G1_zero;
    }
    delete[] quotients_i;
    return;
}

RowProof *Prover::prove_row(int row, bool dummy)
{
    // prove the row
    // in order to prove the content of a row:
    // f(x, y) - f_i(y) = \sum_{j=0}^{log_col-1} (x_j - i_j) * Q(xj+1, ..., y)
    RowProof *new_proof = new RowProof;
    new_proof->row_com = row_coms[row];
    new_proof->qs = new G1[setup->_log_row];

    if (dummy)
    {
        for (int level = 0; level < setup->_log_row; level++)
        {
            new_proof->qs[level] = setup->g1;
        }
        return new_proof;
    }

    for (int level = 0; level < setup->_log_row; level++)
    {
        int block = row >> (setup->_log_row - level);
        new_proof->qs[level] = quotients_trees[level][block];
    }
    return new_proof;
}

RowAux *Prover::generate_aux_for_rows(int *rows, int row_n)
{
    RowAux *aux = new RowAux;
    aux->row_n = row_n;
    aux->log_max_row = setup->_log_row;
    aux->rows = rows; // shallow copy of rows.

    aux->idx_com = new G1[setup->_log_row];

    aux->idx = new F *[setup->_log_row];
    aux->hidx = new G2 *[setup->_log_row];
    aux->h_tmi = new G2 *[setup->_log_row];
    for (int l = 0; l < setup->_log_row; l++)
    {
        aux->idx[l] = new F[row_n];
        aux->hidx[l] = new G2[row_n];
        aux->h_tmi[l] = new G2[row_n];
        aux->idx_com[l] = setup->G1_zero;
        for (int j = 0; j < row_n; j++)
        {
            aux->idx[l][j] = (rows[j] >> (setup->_log_row - 1 - l)) & 1;
            if (aux->idx[l][j] == F_ZERO)
                aux->hidx[l][j] = setup->G2_zero;
            else
            {
                aux->hidx[l][j] = setup->h2;
                aux->idx_com[l] += setup->gipp->ck_g1[j];
            }
        }
        G2 tmp_val = setup->h2tvec[l] - setup->h2;
        for (int k = 0; k < row_n; k++)
        {
            if (aux->idx[l][k] == F_ONE)
                aux->h_tmi[l][k] = tmp_val;
            else
                aux->h_tmi[l][k] = setup->h2tvec[l];
        }
    }
    return aux;
}

MiniMultiRowProof *Prover::_mini_prove_rows(RowAux *aux, Kopis_com<G1> *rows_kcom, bool dummy)
{
    MiniMultiRowProof *proof = new MiniMultiRowProof;
    if (dummy)
    {
        proof->log_max_row = setup->_log_row;
        int log_size = int(ceil(log2(aux->row_n)));
        proof->C_q = new GT[setup->_log_row];
        proof->ip_qh = new GT[setup->_log_row];
        for (int i = 0; i < setup->_log_row; i++)
        {
            proof->C_q[i] = setup->gtr;
            proof->ip_qh[i] = setup->gtr;
        }
        proof->q_batched_tipp_proof = new BatchedTIPP_Proof;
        set_dummy_batched_tipp_proof(proof->q_batched_tipp_proof, setup->_log_row, log_size, setup->g1, setup->h2, setup->gtr, setup->fr);

        proof->cf_mipp_proof = new MIPP_Proof_k;
        set_dummy_mipp_proof_k(proof->cf_mipp_proof, log_size, setup->g1, setup->h2, setup->gtr, setup->fr);

        return proof;
    }
    proof->log_max_row = setup->_log_row;
    proof->rows_kopis_com = rows_kcom->com;
    G1 *sub_row_coms = rows_kcom->row_coms;
    int row_n = aux->row_n;
    RowProof **row_proofs = new RowProof *[row_n];
    G1 **q_table = new G1 *[setup->_log_row];
    for (int j = 0; j < row_n; j++)
    {
        row_proofs[j] = prove_row(aux->rows[j]);
    }

    proof->C_q = new GT[setup->_log_row];

    for (int l = 0; l < setup->_log_row; l++)
    {
        q_table[l] = new G1[row_n];
        for (int j = 0; j < row_n; j++)
        {
            q_table[l][j] = row_proofs[j]->qs[l];
        }
        proof->C_q[l] = ip_G1_G2(q_table[l], setup->gipp->ck_h2, row_n);
    }

    // delete row_proofs:
    for (int i = 0; i < row_n; i++)
        delete row_proofs[i];
    delete[] row_proofs;

    proof->rand_s = non_zero_rand();
    proof->ip_qh = new GT[setup->_log_row];
    G1 *q_s_tmp = new G1[row_n];
    //
    BatchTIPP_Aux tipp_aux;
    tipp_aux.z = proof->ip_qh;
    if (row_n >= 2)
    {
        tipp_aux.zL_0 = new GT[setup->_log_row];
        tipp_aux.zR_0 = new GT[setup->_log_row];
    }
    else
    {
        tipp_aux.zL_0 = nullptr;
        tipp_aux.zR_0 = nullptr;
    }
    for (int l = 0; l < setup->_log_row; l++)
    {
        G1vec_s_power(q_s_tmp, q_table[l], proof->rand_s * proof->rand_s, row_n);
        G1 sum_1 = setup->G1_zero;
        G1 sum_2 = setup->G1_zero;
        G1 sum_1_zL = setup->G1_zero;
        G1 sum_2_zL = setup->G1_zero;
        G1 sum_1_zR = setup->G1_zero;
        G1 sum_2_zR = setup->G1_zero;
        for (int j = 0; j < row_n; j++)
        {
            sum_1 += q_s_tmp[j];
            if (aux->idx[l][j] == F_ONE)
                sum_2 += q_s_tmp[j];
            if (row_n >= 2)
            {
                if (j < row_n / 2)
                {
                    sum_1_zL += q_s_tmp[j + row_n / 2];
                    if (aux->idx[l][j] == F_ONE)
                        sum_2_zL += q_s_tmp[j + row_n / 2];
                }
                else
                {
                    sum_1_zR += q_s_tmp[j - row_n / 2];
                    if (aux->idx[l][j] == F_ONE)
                        sum_2_zR += q_s_tmp[j - row_n / 2];
                }
            }
        }
        proof->ip_qh[l] = my_loop(sum_1, setup->h2tvec[l]) * my_loop(-sum_2, setup->h2);
        if (tipp_aux.zL_0 != nullptr)
        {
            tipp_aux.zL_0[l] = my_loop(sum_1_zL, setup->h2tvec[l]) * my_loop(-sum_2_zL, setup->h2);
            tipp_aux.zR_0[l] = my_loop(sum_1_zR, setup->h2tvec[l]) * my_loop(-sum_2_zR, setup->h2);
        }
    }
    delete[] q_s_tmp;

    F *sq_powers = new F[row_n];
    F s_sq = proof->rand_s * proof->rand_s;
    s_powers(sq_powers, s_sq, row_n);
    proof->rows_com_rlc = ip_F_G1(sq_powers, sub_row_coms, row_n);
    delete[] sq_powers;

    proof->q_batched_tipp_proof = setup->gipp->generate_proof_batched_tipp(q_table, aux->h_tmi, proof->rand_s, row_n, setup->_log_row, &tipp_aux);
    if (tipp_aux.zL_0 != nullptr)
    {
        delete[] tipp_aux.zL_0;
        delete[] tipp_aux.zR_0;
    }
    // delete q_table
    for (int i = 0; i < setup->_log_row; i++)
        delete[] q_table[i];
    delete[] q_table;

    // MIPP

    proof->cf_mipp_proof = setup->gipp->generate_proof_k(sub_row_coms, &s_sq, F_ONE, row_n, false);
    return proof;
}

MultiRowProof *Prover::prove_rows(int *rows, int row_n, G1 *sub_row_coms, bool dummy)
{
    // prove the rows

    // given the rows (idx), can compute C_idx.
    // extract the vector com of f (poly).
    // and the vector com of pi (Q).
    if (row_n != 1 << ((int)ceil(log2(row_n))))
    {
        cout << "row_n should be power of 2" << endl;
        throw "row_n should be power of 2";
    }
    MultiRowProof *proof = new MultiRowProof; // 
    if (dummy)
    {
        proof->row_n = row_n;
        proof->log_max_row = setup->_log_row;
        int log_size = int(ceil(log2(row_n)));
        proof->idx_com = new G1[setup->_log_row];
        proof->C_q = new GT[setup->_log_row];
        proof->ip_qh = new GT[setup->_log_row];
        for (int i = 0; i < setup->_log_row; i++)
        {
            proof->idx_com[i] = setup->g1;
            proof->C_q[i] = setup->gtr;
            proof->ip_qh[i] = setup->gtr;
        }

        proof->q_batched_tipp_proof = new BatchedTIPP_Proof;
        set_dummy_batched_tipp_proof(proof->q_batched_tipp_proof, setup->_log_row, log_size, setup->g1, setup->h2, setup->gtr, setup->fr);
        proof->q_batched_ipa_proof = new BatchedIPA_Proof;
        set_dummy_batched_ipa_proof(proof->q_batched_ipa_proof, setup->_log_row, log_size, setup->g1, setup->h2, setup->gtr, setup->fr);
        proof->cf_mipp_proof = new MIPP_Proof_k;
        set_dummy_mipp_proof_k(proof->cf_mipp_proof, log_size, setup->g1, setup->h2, setup->gtr, setup->fr);

        return proof;
    }
    proof->row_n = row_n;
    proof->log_max_row = setup->_log_row;
    RowProof **row_proofs = new RowProof *[row_n];
    F **idx = new F *[setup->_log_row];

    G2 **h_idx = new G2 *[setup->_log_row];
    proof->idx_com = new G1[setup->_log_row];
    G1 **q_table = new G1 *[setup->_log_row];
    for (int j = 0; j < setup->_log_row; j++)
    {
        idx[j] = new F[row_n];
        h_idx[j] = new G2[row_n];
        q_table[j] = new G1[row_n];
    }
    proof->C_q = new GT[setup->_log_row];

    //  Round 1 | step (1) & (2) | P -> V:  c_pi
    for (int j = 0; j < row_n; j++)
    {
        for (int l = 0; l < setup->_log_row; l++)
        {
            idx[l][j] = (rows[j] >> (setup->_log_row - 1 - l)) & 1;
        }
    }

    for (int l = 0; l < setup->_log_row; l++)
    {
        proof->idx_com[l] = setup->G1_zero;
        for (int j = 0; j < row_n; j++)
        {
            if (idx[l][j] == F_ZERO)
            {
                h_idx[l][j] = setup->G2_zero;
            }
            else
            {
                h_idx[l][j] = setup->h2;
                proof->idx_com[l] += setup->gipp->ck_g1[j];
            }
        }
    }

    for (int j = 0; j < row_n; j++)
    {
        sub_row_coms[j] = this->row_coms[rows[j]];
        row_proofs[j] = this->prove_row(rows[j]);
        for (int l = 0; l < setup->_log_row; l++)
        {
            q_table[l][j] = row_proofs[j]->qs[l];
        }
    }

    // delete row proofs
    for (int i = 0; i < row_n; i++)
        delete row_proofs[i];
    delete[] row_proofs;

    for (int l = 0; l < setup->_log_row; l++)
    {
        proof->C_q[l] = ip_G1_G2(q_table[l], setup->gipp->ck_h2, row_n); // In paper: C_pi[l]
    }

    // Round 2 | step(3) | V -> P: send random s

    proof->rand_s = non_zero_rand();

    // h^{t_l - i_{j,l}}
    G2 **h_tmi = new G2 *[setup->_log_row];
    for (int j = 0; j < setup->_log_row; j++)
    {
        h_tmi[j] = new G2[row_n];
    }
    proof->ip_qh = new GT[setup->_log_row]; // inner product of q and h^{t-i} with rand_s power

    G1 *q_s_tmp = new G1[row_n];
    BatchTIPP_Aux tipp_aux;
    tipp_aux.z = proof->ip_qh; // reference. should not delete.
    if (row_n >= 2)
    {
        tipp_aux.zL_0 = new GT[setup->_log_row];
        tipp_aux.zR_0 = new GT[setup->_log_row];
    }
    else
    {
        tipp_aux.zL_0 = nullptr;
        tipp_aux.zR_0 = nullptr;
    }
    for (int l = 0; l < setup->_log_row; l++)
    {
        G2 tmp_val = setup->h2tvec[l] - setup->h2;
        for (int k = 0; k < row_n; k++)
        {
            if (idx[l][k] == F_ONE)
                h_tmi[l][k] = tmp_val;
            else
                h_tmi[l][k] = setup->h2tvec[l];
        }

        G1vec_s_power(q_s_tmp, q_table[l], proof->rand_s * proof->rand_s, row_n);
        G1 sum_1 = setup->G1_zero;
        G1 sum_2 = setup->G1_zero;
        G1 sum_1_zL = setup->G1_zero;
        G1 sum_2_zL = setup->G1_zero;
        G1 sum_1_zR = setup->G1_zero;
        G1 sum_2_zR = setup->G1_zero;
        for (int j = 0; j < row_n; j++)
        {
            sum_1 += q_s_tmp[j];
            if (idx[l][j] == F_ONE)
                sum_2 += q_s_tmp[j];
            if (row_n >= 2)
            {
                if (j < row_n / 2)
                {
                    sum_1_zL += q_s_tmp[j + row_n / 2];
                    if (idx[l][j] == F_ONE)
                        sum_2_zL += q_s_tmp[j + row_n / 2];
                }
                else
                {
                    sum_1_zR += q_s_tmp[j - row_n / 2];
                    if (idx[l][j] == F_ONE)
                        sum_2_zR += q_s_tmp[j - row_n / 2];
                }
            }
        }
        proof->ip_qh[l] = my_loop(sum_1, setup->h2tvec[l]) * my_loop(-sum_2, setup->h2);
        if (tipp_aux.zL_0 != nullptr)
        {
            tipp_aux.zL_0[l] = my_loop(sum_1_zL, setup->h2tvec[l]) * my_loop(-sum_2_zL, setup->h2);
            tipp_aux.zR_0[l] = my_loop(sum_1_zR, setup->h2tvec[l]) * my_loop(-sum_2_zR, setup->h2);
        }
    }
    delete[] q_s_tmp;

    // delete h_idx
    for (int j = 0; j < setup->_log_row; j++)
    {
        delete[] h_idx[j];
    }
    delete[] h_idx;

    proof->rows_kopis_com = ip_G1_G2(sub_row_coms, setup->gipp->ck_h2, row_n); // C_F
    F *sq_powers = new F[row_n];
    s_powers(sq_powers, proof->rand_s * proof->rand_s, row_n);
    proof->rows_com_rlc = ip_F_G1(sq_powers, sub_row_coms, row_n); // Step 4(1) C_aggr
    delete[] sq_powers;

    // Round 3 | P->V | send poly_t_rlc and ip_qh to V
    // Large Round 4 run l TIPPs | Step 5
    proof->q_batched_tipp_proof = setup->gipp->generate_proof_batched_tipp(q_table, h_tmi, proof->rand_s, row_n, setup->_log_row, &tipp_aux);
    if (tipp_aux.zL_0 != nullptr)
    {
        delete[] tipp_aux.zL_0;
        delete[] tipp_aux.zR_0;
    }

    // delete h_tmi not used anymore
    for (int j = 0; j < setup->_log_row; j++)
        delete h_tmi[j];
    delete[] h_tmi;

    // delete q_table
    for (int j = 0; j < setup->_log_row; j++)
    {
        delete[] q_table[j];
    }
    delete[] q_table;

    // Large Round 4 run MIPP
    F s_sq = proof->rand_s * proof->rand_s;
    proof->cf_mipp_proof = setup->gipp->generate_proof_k(sub_row_coms, &s_sq, F_ONE, row_n, false);

    // Step 6 only in verifier.
    // Round 5 | V->P | another randomness, log_size | Step 7
    proof->rand_s_i = non_zero_rand();

    F **cons1 = new F *[setup->_log_row];
    for (int l = 0; l < setup->_log_row; l++)
    {
        cons1[l] = new F[row_n];
        for (int j = 0; j < row_n; j++)
        {
            cons1[l][j] = F_ONE - idx[l][j];
        }
    }
    proof->q_batched_ipa_proof = setup->gipp->generate_proof_batched_ipa(idx, cons1, proof->rand_s_i, row_n, setup->_log_row);

    for (int l = 0; l < setup->_log_row; l++)
    {
        delete[] cons1[l];
        delete[] idx[l];
    }
    delete[] cons1;
    delete[] idx;

    return proof;
}

void Prover::update_row(int row, F *row_data, int data_col, G1 *row_com, bool dummy)
{
    if (dummy)
        return;
    G1 new_row_com;
    if (row_com == nullptr)
    {
        setup->logcol_kzg->commit(new_row_com, row_data, setup->_log_col, data_col);
    }
    else
    {
        new_row_com = *row_com;
    }
    F *data_diff = new F[setup->_max_col];
    for (int col_i = 0; col_i < data_col; col_i++)
    {
        data_diff[col_i] = row_data[col_i] - _data[row][col_i];
    }
    G1 new_row_beta_com = multi_beta_rowi_f_T(row_data, setup->g1tvec_tower_all[0], row, setup->_log_col, data_col);

    G1 diff_row_com = new_row_com - row_coms[row];
    G1 *diff_quotients_i = new G1[setup->_log_row];
    multi_hyper_of_f_as_rowi(diff_quotients_i, data_diff, row, setup->_log_row, setup->_log_col, setup->g1tvec_tower_all, &diff_row_com, setup->_max_col);

    for (int level = 0; level < setup->_log_row; level++)
    {

        int block = row >> (setup->_log_row - level);
        quotients_trees[level][block] += diff_quotients_i[level];
    }
    delete[] diff_quotients_i;
    table_com += new_row_beta_com - row_beta_coms[row];
    row_coms[row] = new_row_com;
    row_beta_coms[row] = new_row_beta_com;
    for (int col_i = 0; col_i < data_col; col_i++)
    {
        _data[row][col_i] = row_data[col_i];
    }
    for (int col_i = data_col; col_i < setup->_max_col; col_i++)
    {
        _data[row][col_i] = F_ZERO;
    }
    delete[] data_diff;
}

UpdateRowsProof *Prover::update_rows(int *rows, F **new_data, int row_n, bool dummy)
{
    int log_k = int(ceil(log2(row_n)));
    UpdateRowsProof *proof = new UpdateRowsProof;

    // idx related:

    RowAux *aux = generate_aux_for_rows(rows, row_n);
    proof->idx = aux->idx;
    proof->idx_kcom = new Kopis_com<G2> *[setup->_log_row]; // hidx[l] = idx_kcom[l].row_coms
    for (int l = 0; l < setup->_log_row; l++)
    {
        proof->idx_kcom[l] = new Kopis_com<G2>;
        proof->idx_kcom[l]->com = my_loop(aux->idx_com[l], setup->kopis_g2->kzg->h);
        proof->idx_kcom[l]->row_coms = aux->hidx[l];
        proof->idx_kcom[l]->size = row_n;
    }
    proof->idx_com = aux->idx_com;
    proof->row_n = row_n;
    proof->log_max_row = setup->_log_row;

    F **old_data_ptr = new F *[row_n];
    for (int j = 0; j < row_n; j++)
    {
        old_data_ptr[j] = new F[setup->_max_col];
        memcpy(old_data_ptr[j], _data[rows[j]], setup->_max_col * sizeof(F));
    }

    G1 *old_sub_row_coms = new G1[row_n];
    for (int j = 0; j < row_n; j++)
    {
        old_sub_row_coms[j] = row_coms[rows[j]];
    }

    proof->old_F_kopis_com = setup->kopis->commit(old_data_ptr, row_n, setup->_log_col, setup->_max_col, old_sub_row_coms); // avoid computing row com again.
    delete[] old_sub_row_coms;                                                                                              // use old_F_kopis_com->row_coms instead.
    proof->new_F_kopis_com = setup->kopis->commit(new_data, row_n, setup->_log_col, setup->_max_col);                       // here computes row com already, avoid computing row com in update

    // lookup on the old parts;
    proof->old_proof = _mini_prove_rows(aux, proof->old_F_kopis_com, dummy);
    // compute the old delta(x, y) and the new delta'(x, y). What matters is the commitment. (t val).
    // G1 old_table_com = table_com;

    proof->old_delta_com = setup->G1_zero;
    for (int j = 0; j < row_n; j++)
    {
        proof->old_delta_com += row_beta_coms[rows[j]];
    }

    for (int i = 0; i < row_n; i++)
    {
        update_row(rows[i], new_data[i], setup->_max_col, &proof->new_F_kopis_com->row_coms[i], dummy);
    }
    proof->new_proof = _mini_prove_rows(aux, proof->new_F_kopis_com, dummy);

    G1 *new_rows = new G1[row_n];
    proof->new_delta_com = setup->G1_zero;
    for (int j = 0; j < row_n; j++)
    {
        new_rows[j] = row_coms[rows[j]];
        proof->new_delta_com += row_beta_coms[rows[j]];
    }

    // prepare beta_com compute

    F **beta_polys = new F *[row_n];

    for (int j = 0; j < row_n; j++)
    {
        beta_polys[j] = new F[setup->_max_row];
        for (int i = 0; i < setup->_max_row; i++)
        {
            beta_polys[j][i] = F_ZERO;
        }
        beta_polys[j][rows[j]] = F_ONE;
    }
    Kopis_com<G2> *beta_kcom = setup->kopis_g2->commit(beta_polys, row_n, setup->_log_row, setup->_max_row);

    proof->beta_kcom = beta_kcom;

    proof->r1 = new F[log_k + setup->_log_row];
    for (int i = 0; i < log_k + setup->_log_row; i++)
        proof->r1[i] = F(rand());
    proof->r2 = proof->r1 + log_k;
    proof->beta_r1_r2_open = setup->kopis_g2->Kopisopen(beta_polys, proof->r1, proof->r2, beta_kcom, setup->_log_row);

    for (int j = 0; j < row_n; j++)
    {
        delete[] beta_polys[j];
    }
    delete[] beta_polys;

    // delete old_data
    for (int j = 0; j < row_n; j++)
    {
        delete[] old_data_ptr[j];
    }
    delete[] old_data_ptr;

    GT old_delta_com_h = my_loop(proof->old_delta_com, setup->h2);
    GT new_delta_com_h = my_loop(proof->new_delta_com, setup->h2);
    proof->old_delta_tipp = setup->gipp->generate_proof_tipp(proof->old_F_kopis_com->row_coms, beta_kcom->row_coms, F_ONE, row_n, &old_delta_com_h);
    proof->new_delta_tipp = setup->gipp->generate_proof_tipp(new_rows, beta_kcom->row_coms, F_ONE, row_n, &new_delta_com_h);

    delete[] new_rows;
    delete aux;
    return proof;
}

UpdateRowsProof_New *Prover::update_rows_new(int *rows, F **new_data, int row_n, bool dummy)
{
    high_resolution_clock::time_point t1, t2;
    UpdateRowsProof_New *proof = new UpdateRowsProof_New;
    int log_k = int(ceil(log2(row_n)));

    // Step 0: idx related
    RowAux *aux = generate_aux_for_rows(rows, row_n);
    proof->idx = aux->idx;
    proof->idx_com = aux->idx_com;

    proof->idx_kcom = new Kopis_com<G2> *[setup->_log_row]; // hidx[l] = idx_kcom[l].row_coms
    for (int l = 0; l < setup->_log_row; l++)
    {
        proof->idx_kcom[l] = new Kopis_com<G2>;
        proof->idx_kcom[l]->com = my_loop(aux->idx_com[l], setup->kopis_g2->kzg->h);
        proof->idx_kcom[l]->row_coms = aux->hidx[l];
        proof->idx_kcom[l]->size = row_n;
    }
    proof->row_n = row_n;
    proof->log_max_row = setup->_log_row;

    // Round1 - Step1

    F **old_data_ptr = new F *[row_n];
    for (int j = 0; j < row_n; j++)
    {
        old_data_ptr[j] = new F[setup->_max_col];
        memcpy(old_data_ptr[j], _data[rows[j]], setup->_max_col * sizeof(F));
    }
    G1 *old_sub_row_coms = new G1[row_n];
    for (int j = 0; j < row_n; j++)
    {
        old_sub_row_coms[j] = row_coms[rows[j]];
    }

    proof->old_F_kopis_com = setup->kopis->commit(old_data_ptr, row_n, setup->_log_col, setup->_max_col, old_sub_row_coms); // avoid computing row com again.
    delete[] old_sub_row_coms;
    proof->new_F_kopis_com = setup->kopis->commit(new_data, row_n, setup->_log_col, setup->_max_col); // here computs row com already, avoid computing row com in update

    // save data of old F

    // Step 2

    proof->old_proof = _mini_prove_rows(aux, proof->old_F_kopis_com, dummy);

    proof->old_delta_com = setup->G1_zero;
    for (int j = 0; j < row_n; j++)
    {
        proof->old_delta_com += row_beta_coms[rows[j]];
    }
    // Step 3 update aux
    for (int i = 0; i < row_n; i++)
    {
        update_row(rows[i], new_data[i], setup->_max_col, &proof->new_F_kopis_com->row_coms[i], dummy);
    }
    // Step 4
    proof->new_proof = _mini_prove_rows(aux, proof->new_F_kopis_com, dummy);

    //

    // Step 6: P->V send C_old_delta and C_new_delta

    proof->new_delta_com = setup->G1_zero;
    for (int j = 0; j < row_n; j++)
    {
        proof->new_delta_com += row_beta_coms[rows[j]];
    }

    // Step 7: P->V send r1, r2,
    proof->r1 = new F[setup->_log_row + setup->_log_col];
    for (int i = 0; i < setup->_log_row + setup->_log_col; i++)
        proof->r1[i] = F(rand());
    proof->r2 = proof->r1 + setup->_log_row;

    // Step 8: P->V y_old_delta, y_new_delta, y_old_proof, y_new_proof
    // open delta(x, y) \sum_{j\in rows} beta(x, j) f_j(y) at point (r1, r2)
    // think about each j, open beta(x, j)f_j(y).
    // beta(x,j)*f_j(y) - beta(r1, j)*f_j(r2) = beta(x,j)*f_j(y) - beta(r1, j)*f_j(y) + beta(r1, j)*f_j(y) - beta(r1, j)*f_j(r2)
    // = (beta(x,j) - beta(r1, j))f_j(y) + beta(r1, j)(f_j(y) - f_j(r2))
    //

    if (row_n * 10 < setup->_max_row)
    {
        t1 = high_resolution_clock::now();
        proof->y_old_delta = F_ZERO;
        proof->y_old_proof = new G1[setup->_log_row + setup->_log_col];
        for (int l = 0; l < setup->_log_row + setup->_log_col; l++)
            proof->y_old_proof[l] = setup->G1_zero;
        G1 *qs = new G1[setup->_log_row + setup->_log_col];
        for (int j = 0; j < row_n; j++)
        {
            proof->y_old_delta += multi_eval(old_data_ptr[j], proof->r2, setup->_log_col, setup->_max_col) * beta(proof->r1, rows[j], setup->_log_row);
            multi_Q_of_beta_rowi_f(qs, old_data_ptr[j], proof->r1, rows[j], setup->_log_row, setup->_log_col, setup->g1tvec_tower_all, setup->g1, setup->_max_col);

            G1vec_add(proof->y_old_proof, proof->y_old_proof, qs, setup->_log_row + setup->_log_col);
        }
        delete[] qs;
        t2 = high_resolution_clock::now();
        cout << "old method of old_delta in time: " << get_time(t1, t2) << " seconds" << endl;
    }
    else
    {
        t1 = high_resolution_clock::now();
        F *old_delta_poly = new F[setup->_max_row * setup->_max_col];
        for (int i = 0; i < setup->_max_row * setup->_max_col; i++)
        {
            old_delta_poly[i] = F_ZERO;
        }
        for (int j = 0; j < row_n; j++)
        {
            for (int i = 0; i < setup->_max_col; i++)
            {
                old_delta_poly[rows[j] * setup->_max_col + i] = old_data_ptr[j][i];
            }
        }
        proof->y_old_delta = multi_eval(old_delta_poly, proof->r1, setup->_log_row + setup->_log_col, setup->_max_row * setup->_max_col);
        proof->y_old_proof = new G1[setup->_log_row + setup->_log_col];
        multi_Q_of_f(proof->y_old_proof, old_delta_poly, proof->r1, setup->_log_row + setup->_log_col, setup->g1tvec_tower_all, setup->g1);
        delete[] old_delta_poly;
        t2 = high_resolution_clock::now();
        cout << "new method of old_delta in time: " << get_time(t1, t2) << " seconds" << endl;
    }

    // delete temp old subtable
    for (int j = 0; j < row_n; j++)
    {
        delete[] old_data_ptr[j];
    }
    delete[] old_data_ptr;

    if (row_n * 10 < setup->_max_row)
    {
        proof->y_new_delta = F_ZERO;
        proof->y_new_proof = new G1[setup->_log_row + setup->_log_col];
        for (int l = 0; l < setup->_log_row + setup->_log_col; l++)
            proof->y_new_proof[l] = setup->G1_zero;
        G1 *qs = new G1[setup->_log_row + setup->_log_col];
        for (int j = 0; j < row_n; j++)
        {
            proof->y_new_delta += multi_eval(new_data[j], proof->r2, setup->_log_col, setup->_max_col) * beta(proof->r1, rows[j], setup->_log_row);
            multi_Q_of_beta_rowi_f(qs, new_data[j], proof->r1, rows[j], setup->_log_row, setup->_log_col, setup->g1tvec_tower_all, setup->g1, setup->_max_col);
            G1vec_add(proof->y_new_proof, proof->y_new_proof, qs, setup->_log_row + setup->_log_col);
        }
        delete[] qs;
    }
    else
    {
        F *new_delta_poly = new F[setup->_max_row * setup->_max_col];
        for (int i = 0; i < setup->_max_row * setup->_max_col; i++)
        {
            new_delta_poly[i] = F_ZERO;
        }
        for (int j = 0; j < row_n; j++)
        {
            for (int i = 0; i < setup->_max_col; i++)
            {
                new_delta_poly[rows[j] * setup->_max_col + i] = new_data[j][i];
            }
        }
        proof->y_new_delta = multi_eval(new_delta_poly, proof->r1, setup->_log_row + setup->_log_col, setup->_max_row * setup->_max_col);
        proof->y_new_proof = new G1[setup->_log_row + setup->_log_col];
        multi_Q_of_f(proof->y_new_proof, new_delta_poly, proof->r1, setup->_log_row + setup->_log_col, setup->g1tvec_tower_all, setup->g1);
        delete[] new_delta_poly;
    }
    // step 9. CP-SNARK

    delete aux;

    return proof;
}

UpdateRowsProof_NewNew *Prover::update_rows_newnew(int *rows, F **new_data, int row_n, bool dummy)
{
    high_resolution_clock::time_point t1, t2;
    UpdateRowsProof_NewNew *proof = new UpdateRowsProof_NewNew;
    int log_k = int(ceil(log2(row_n)));

    // Step 0: idx related
    RowAux *aux = generate_aux_for_rows(rows, row_n);
    proof->idx = aux->idx;
    proof->idx_com = aux->idx_com;

    proof->idx_kcom = new Kopis_com<G2> *[setup->_log_row]; // hidx[l] = idx_kcom[l].row_coms
    for (int l = 0; l < setup->_log_row; l++)
    {
        proof->idx_kcom[l] = new Kopis_com<G2>;
        proof->idx_kcom[l]->com = my_loop(aux->idx_com[l], setup->kopis_g2->kzg->h);
        proof->idx_kcom[l]->row_coms = aux->hidx[l];
        proof->idx_kcom[l]->size = row_n;
    }
    proof->row_n = row_n;
    proof->log_max_row = setup->_log_row;

    // Round1 - Step1

    F **old_data_ptr = new F *[row_n];
    for (int j = 0; j < row_n; j++)
    {
        old_data_ptr[j] = new F[setup->_max_col];
        memcpy(old_data_ptr[j], _data[rows[j]], setup->_max_col * sizeof(F));
    }
    G1 *old_sub_row_coms = new G1[row_n];
    for (int j = 0; j < row_n; j++)
    {
        old_sub_row_coms[j] = row_coms[rows[j]];
    }

    proof->old_F_kopis_com = setup->kopis->commit(old_data_ptr, row_n, setup->_log_col, setup->_max_col, old_sub_row_coms); // avoid computing row com again.
    delete[] old_sub_row_coms;
    proof->new_F_kopis_com = setup->kopis->commit(new_data, row_n, setup->_log_col, setup->_max_col); // here computs row com already, avoid computing row com in update

    // save data of old F

    // Step 2
    proof->rand_lookup = F(rand());

    proof->lookup_proof = new MiniMultiRowProof;
    GT::pow(proof->lookup_proof->rows_kopis_com, proof->new_F_kopis_com->com, proof->rand_lookup);
    proof->lookup_proof->rows_kopis_com = proof->lookup_proof->rows_kopis_com * proof->old_F_kopis_com->com;
    // to construct q:
    G1 **q_table = new G1 *[setup->_log_row];
    for (int l = 0; l < setup->_log_row; l++)
    {
        q_table[l] = new G1[row_n];
    }
    RowProof *row_proof;
    for (int j = 0; j < row_n; j++)
    {
        row_proof = prove_row(rows[j], dummy);
        for (int l = 0; l < setup->_log_row; l++)
        {
            q_table[l][j] = row_proof->qs[l]; // note that q in code = \pi in paper
        }
        delete row_proof;
    }
    G1 *tilde_row_coms = new G1[row_n];
    memcpy(tilde_row_coms, proof->old_F_kopis_com->row_coms, row_n * sizeof(G1));
    for (int j = 0; j < row_n; j++)
    {
        tilde_row_coms[j] += proof->new_F_kopis_com->row_coms[j] * proof->rand_lookup;
    }

    proof->old_delta_com = setup->G1_zero;
    for (int j = 0; j < row_n; j++)
    {
        proof->old_delta_com += row_beta_coms[rows[j]];
    }
    // Step 3 update aux
    for (int i = 0; i < row_n; i++)
    {
        update_row(rows[i], new_data[i], setup->_max_col, &proof->new_F_kopis_com->row_coms[i], dummy);
    }
    // Step 4

    for (int j = 0; j < row_n; j++)
    {
        row_proof = prove_row(rows[j], dummy);
        for (int l = 0; l < setup->_log_row; l++)
        {
            q_table[l][j] += row_proof->qs[l] * proof->rand_lookup; // note that q in code = \pi in paper
        }
        delete row_proof;
    }
    // now q_table is tilde{q} = q + r * q'
    proof->lookup_proof->C_q = new GT[setup->_log_row];
    for (int l = 0; l < setup->_log_row; l++)
    {
        proof->lookup_proof->C_q[l] = ip_G1_G2(q_table[l], setup->gipp->ck_h2, row_n);
    }
    proof->lookup_proof->rand_s = non_zero_rand();
    // compute ip_qh and tipp_aux
    G1 *q_s_tmp = new G1[row_n];
    proof->lookup_proof->ip_qh = new GT[setup->_log_row];
    BatchTIPP_Aux tipp_aux;
    tipp_aux.z = proof->lookup_proof->ip_qh;
    if (row_n >= 2)
    {
        tipp_aux.zL_0 = new GT[setup->_log_row];
        tipp_aux.zR_0 = new GT[setup->_log_row];
    }
    else
    {
        tipp_aux.zL_0 = nullptr;
        tipp_aux.zR_0 = nullptr;
    }
    F rand_s = proof->lookup_proof->rand_s;
    F rand_s_sq = rand_s * rand_s;
    for (int l = 0; l < setup->_log_row; l++)
    {
        G1vec_s_power(q_s_tmp, q_table[l], rand_s_sq, row_n);
        G1 sum_1 = setup->G1_zero;
        G1 sum_2 = setup->G1_zero;
        G1 sum_1_zL = setup->G1_zero;
        G1 sum_2_zL = setup->G1_zero;
        G1 sum_1_zR = setup->G1_zero;
        G1 sum_2_zR = setup->G1_zero;
        for (int j = 0; j < row_n; j++)
        {
            sum_1 += q_s_tmp[j];
            if (aux->idx[l][j] == F_ONE)
                sum_2 += q_s_tmp[j];
            if (row_n >= 2)
            {
                if (j < row_n / 2)
                {
                    sum_1_zL += q_s_tmp[j + row_n / 2];
                    if (aux->idx[l][j] == F_ONE)
                        sum_2_zL += q_s_tmp[j + row_n / 2];
                }
                else
                {
                    sum_1_zR += q_s_tmp[j - row_n / 2];
                    if (aux->idx[l][j] == F_ONE)
                        sum_2_zR += q_s_tmp[j - row_n / 2];
                }
            }
        }
        proof->lookup_proof->ip_qh[l] = my_loop(sum_1, setup->h2tvec[l]) * my_loop(-sum_2, setup->h2);
        if (tipp_aux.zL_0 != nullptr)
        {
            tipp_aux.zL_0[l] = my_loop(sum_1_zL, setup->h2tvec[l]) * my_loop(-sum_2_zL, setup->h2);
            tipp_aux.zR_0[l] = my_loop(sum_1_zR, setup->h2tvec[l]) * my_loop(-sum_2_zR, setup->h2);
        }
    }
    delete[] q_s_tmp;

    F *sq_powers = new F[row_n];
    s_powers(sq_powers, rand_s_sq, row_n);
    proof->lookup_proof->rows_com_rlc = ip_F_G1(sq_powers, tilde_row_coms, row_n);
    delete[] sq_powers;

    proof->lookup_proof->q_batched_tipp_proof = setup->gipp->generate_proof_batched_tipp(q_table, aux->h_tmi, proof->lookup_proof->rand_s, row_n, setup->_log_row, &tipp_aux);
    if (tipp_aux.zL_0 != nullptr)
    {
        delete[] tipp_aux.zL_0;
        delete[] tipp_aux.zR_0;
    }
    // delete q_table
    for (int j = 0; j < setup->_log_row; j++)
        delete[] q_table[j];
    delete[] q_table;

    // mipp
    proof->lookup_proof->cf_mipp_proof = setup->gipp->generate_proof_k(tilde_row_coms, &rand_s_sq, F_ONE, row_n, false);

    // Step 5

    // Step 6: P->V send C_old_delta and C_new_delta

    proof->new_delta_com = setup->G1_zero;
    for (int j = 0; j < row_n; j++)
    {
        proof->new_delta_com += row_beta_coms[rows[j]];
    }

    // Step 7: P->V send r1, r2,
    proof->r1 = new F[setup->_log_row + setup->_log_col];
    for (int i = 0; i < setup->_log_row + setup->_log_col; i++)
        proof->r1[i] = F(rand());
    proof->r2 = proof->r1 + setup->_log_row;

    // Step 8: P->V y_old_delta, y_new_delta, y_old_proof, y_new_proof
    // open delta(x, y) \sum_{j\in rows} beta(x, j) f_j(y) at point (r1, r2)
    // think about each j, open beta(x, j)f_j(y).
    // beta(x,j)*f_j(y) - beta(r1, j)*f_j(r2) = beta(x,j)*f_j(y) - beta(r1, j)*f_j(y) + beta(r1, j)*f_j(y) - beta(r1, j)*f_j(r2)
    // = (beta(x,j) - beta(r1, j))f_j(y) + beta(r1, j)(f_j(y) - f_j(r2))
    //
    if (row_n * 10 < setup->_max_row)
    {
        t1 = high_resolution_clock::now();
        proof->y_old_delta = F_ZERO;
        proof->y_old_proof = new G1[setup->_log_row + setup->_log_col];
        for (int l = 0; l < setup->_log_row + setup->_log_col; l++)
            proof->y_old_proof[l] = setup->G1_zero;
        G1 *qs = new G1[setup->_log_row + setup->_log_col];
        for (int j = 0; j < row_n; j++)
        {
            proof->y_old_delta += multi_eval(old_data_ptr[j], proof->r2, setup->_log_col, setup->_max_col) * beta(proof->r1, rows[j], setup->_log_row);
            multi_Q_of_beta_rowi_f(qs, old_data_ptr[j], proof->r1, rows[j], setup->_log_row, setup->_log_col, setup->g1tvec_tower_all, setup->g1, setup->_max_col);

            G1vec_add(proof->y_old_proof, proof->y_old_proof, qs, setup->_log_row + setup->_log_col);
        }
        delete[] qs;
        t2 = high_resolution_clock::now();
        cout << "old method of old_delta in time: " << get_time(t1, t2) << " seconds" << endl;
    }
    else
    {
        t1 = high_resolution_clock::now();
        F *old_delta_poly = new F[setup->_max_row * setup->_max_col];
        for (int i = 0; i < setup->_max_row * setup->_max_col; i++)
        {
            old_delta_poly[i] = F_ZERO;
        }
        for (int j = 0; j < row_n; j++)
        {
            for (int i = 0; i < setup->_max_col; i++)
            {
                old_delta_poly[rows[j] * setup->_max_col + i] = old_data_ptr[j][i];
            }
        }
        proof->y_old_delta = multi_eval(old_delta_poly, proof->r1, setup->_log_row + setup->_log_col, setup->_max_row * setup->_max_col);
        proof->y_old_proof = new G1[setup->_log_row + setup->_log_col];
        multi_Q_of_f(proof->y_old_proof, old_delta_poly, proof->r1, setup->_log_row + setup->_log_col, setup->g1tvec_tower_all, setup->g1);
        delete[] old_delta_poly;
        t2 = high_resolution_clock::now();
        cout << "new method of old_delta in time: " << get_time(t1, t2) << " seconds" << endl;
    }

    // delete temp old subtable
    for (int j = 0; j < row_n; j++)
    {
        delete[] old_data_ptr[j];
    }
    delete[] old_data_ptr;

    if (row_n * 10 < setup->_max_row)
    {
        proof->y_new_delta = F_ZERO;
        proof->y_new_proof = new G1[setup->_log_row + setup->_log_col];
        for (int l = 0; l < setup->_log_row + setup->_log_col; l++)
            proof->y_new_proof[l] = setup->G1_zero;
        G1 *qs = new G1[setup->_log_row + setup->_log_col];
        for (int j = 0; j < row_n; j++)
        {
            proof->y_new_delta += multi_eval(new_data[j], proof->r2, setup->_log_col, setup->_max_col) * beta(proof->r1, rows[j], setup->_log_row);
            multi_Q_of_beta_rowi_f(qs, new_data[j], proof->r1, rows[j], setup->_log_row, setup->_log_col, setup->g1tvec_tower_all, setup->g1, setup->_max_col);
            G1vec_add(proof->y_new_proof, proof->y_new_proof, qs, setup->_log_row + setup->_log_col);
        }
        delete[] qs;
    }
    else
    {
        F *new_delta_poly = new F[setup->_max_row * setup->_max_col];
        for (int i = 0; i < setup->_max_row * setup->_max_col; i++)
        {
            new_delta_poly[i] = F_ZERO;
        }
        for (int j = 0; j < row_n; j++)
        {
            for (int i = 0; i < setup->_max_col; i++)
            {
                new_delta_poly[rows[j] * setup->_max_col + i] = new_data[j][i];
            }
        }
        proof->y_new_delta = multi_eval(new_delta_poly, proof->r1, setup->_log_row + setup->_log_col, setup->_max_row * setup->_max_col);
        proof->y_new_proof = new G1[setup->_log_row + setup->_log_col];
        multi_Q_of_f(proof->y_new_proof, new_delta_poly, proof->r1, setup->_log_row + setup->_log_col, setup->g1tvec_tower_all, setup->g1);
        delete[] new_delta_poly;
    }
    // step 9. CP-SNARK

    // delete aux
    delete aux;
    return proof;
}
