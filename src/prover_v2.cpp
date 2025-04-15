#include "prover_v2.hpp"

Prover_v2::Prover_v2(Setup *setup)
{
    this->setup = setup;
}

Prover_v2::~Prover_v2()
{
    delete chunks_kcom;
    for (int i = 0; i < _n_chunks; i++)
    {
        delete chunk_provers[i];
    }
    delete[] chunk_provers;
}

int size_of_lookup_proof(int _log_table_row, int _log_chunk_size, int _log_col, int row_n)
{
    int log_size = int(ceil(log2(row_n)));
    int size = 0;
    // ignore rows_kopis_com  
    size += sizeof(G1) + sizeof(int) + sizeof(int); 
    size += sizeof(G1*) + sizeof(G1) * (_log_table_row); // idx_com
    size += sizeof(G1*) + sizeof(G1) * (_log_chunk_size); // C_q
    size += sizeof(G1*) + sizeof(G1) * (_log_chunk_size); // ip_qh

    G1 g1r;
    G2 h2r; 
    GT gtr;
    F fr = non_zero_rand();
    hashAndMapToG1(g1r, "rand_g1");
    hashAndMapToG2(h2r, "rand_g2");
    gtr = my_pairing(g1r, h2r);
    
    BatchedTIPP_Proof*b_tipp_proof = new BatchedTIPP_Proof;
    set_dummy_batched_tipp_proof(b_tipp_proof, _log_chunk_size, log_size, g1r, h2r, gtr, fr);
    size += b_tipp_proof->size_in_bytes(); // q_batched_tipp_proof
    delete b_tipp_proof;
    
    MIPP_Proof_k *dummy_proof_k = new MIPP_Proof_k;
    set_dummy_mipp_proof_k(dummy_proof_k, _log_chunk_size, g1r, h2r, gtr, fr);
    size += dummy_proof_k->size_in_bytes(); // q_mipp_proof
    delete dummy_proof_k;

    MIPP_Proof* dummy_proof = new MIPP_Proof;
    set_dummy_mipp_proof(dummy_proof, _log_chunk_size, g1r, h2r, gtr, fr);
    size += dummy_proof->size_in_bytes(); // q_mipp_proof
    delete dummy_proof;

    size += sizeof(G1) + sizeof(F) + sizeof(F); 

    BatchedIPA_Proof *dummy_proof_ipa = new BatchedIPA_Proof;
    set_dummy_batched_ipa_proof(dummy_proof_ipa, _log_chunk_size, log_size, g1r, h2r, gtr, fr);
    size += dummy_proof_ipa->size_in_bytes(); // cf_mipp_proof
    delete dummy_proof_ipa;
    return size; 
}

int size_of_mini_lookup_proof(int _log_table_row, int _log_chunk_size, int _log_col, int row_n)
{
    int log_size = int(ceil(log2(row_n)));
    int size = 0; 
    // ignore rows_kopis_com
    size += sizeof(G1);
    size += sizeof(G1*) + sizeof(G1) * (_log_chunk_size); // C_q
    size += sizeof(G1*) + sizeof(G1) * (_log_chunk_size); // ip_qh

    G1 g1r;
    G2 h2r; 
    GT gtr;
    F fr = non_zero_rand();
    hashAndMapToG1(g1r, "rand_g1");
    hashAndMapToG2(h2r, "rand_g2");
    gtr = my_pairing(g1r, h2r);
    
    BatchedTIPP_Proof*b_tipp_proof = new BatchedTIPP_Proof;
    set_dummy_batched_tipp_proof(b_tipp_proof, _log_chunk_size, log_size, g1r, h2r, gtr, fr);
    size += b_tipp_proof->size_in_bytes(); // q_batched_tipp_proof
    delete b_tipp_proof;
    
    MIPP_Proof_k *dummy_proof_k = new MIPP_Proof_k;
    set_dummy_mipp_proof_k(dummy_proof_k, _log_chunk_size, g1r, h2r, gtr, fr);
    size += dummy_proof_k->size_in_bytes(); // q_mipp_proof
    delete dummy_proof_k;

    MIPP_Proof* dummy_proof = new MIPP_Proof;
    set_dummy_mipp_proof(dummy_proof, _log_chunk_size, g1r, h2r, gtr, fr);
    size += dummy_proof->size_in_bytes(); // q_mipp_proof
    delete dummy_proof;

    size += sizeof(G1) + sizeof(int) + sizeof(F); 
    return size; 
}

// use newnew_v2 version
int size_of_update_proof(int _log_table_row, int _log_chunk_size, int _log_col, int row_n)
{
    int log_size = int(ceil(log2(row_n)));
    int size = 0;
    size += sizeof(int) + sizeof(int); 
    size += sizeof(G1*) + sizeof(G1) * (_log_table_row); // idx_com
    
    size += sizeof(F); 
    size += size_of_mini_lookup_proof(_log_table_row, _log_chunk_size, _log_col, row_n);
    size += sizeof(GT) * 2; // old new delta_com 
    size += sizeof(F*) + sizeof(F) * (_log_table_row + _log_col); // r1 r2
    size += size_of_Kopis_open(row_n, _log_chunk_size + _log_col) * 2;
    return size; 
}

void Prover_v2::init(F **data, int row_size, int col_size, bool dummy)
{
    this->_n_chunks = row_size / setup->_max_row;
    this->_log_n_chunks = int(ceil(log2(_n_chunks)));
    cout << "row_size = " << row_size << " col_size = " << col_size << " n_chunks = " << _n_chunks << endl;
    cout << "max_chunks = " << setup->_max_chunks << " max_row = " << setup->_max_row << endl;
    assert((void("prover_v2::init: row_size should be equal to setup->_max_row * n_chunks"), row_size == setup->_max_row * setup->_max_chunks));
    this->_table_row = row_size;
    this->_log_table_row = int(ceil(log2(_table_row)));

    this->_chunk_size = setup->_max_row;
    this->_log_chunk_size = setup->_log_row;

    chunk_provers = new Prover *[_n_chunks];
    chunks_kcom = new Kopis_com<G1>;
    chunks_kcom->row_coms = new G1[_n_chunks]; // memory: moved to chunks_kcom

    for (int i = 0; i < _n_chunks; i++)
    {
        chunk_provers[i] = new Prover(setup);
        chunk_provers[i]->init(data + i * _chunk_size, _chunk_size, col_size, dummy);
        chunks_kcom->row_coms[i] = chunk_provers[i]->table_com;
    }
    if (dummy)
        chunks_kcom->com = setup->gtr;
    else
        chunks_kcom->com = ip_G1_G2(chunks_kcom->row_coms, setup->gipp->ck_h2, _n_chunks);
    chunks_kcom->size = _n_chunks;
    return;
}

RowProof_v2 *Prover_v2::prove_row(int row, bool dummy)
{
    RowProof_v2 *new_proof = new RowProof_v2;
    // first find the chunk
    int chunk_i = row / _chunk_size;
    int row_i = row % _chunk_size;
    if (dummy)
    {
        // generate dummy MIPP_Proof_k proof
        MIPP_Proof_k *dummy_proof = new MIPP_Proof_k;
        set_dummy_mipp_proof_k(dummy_proof, _log_chunk_size, setup->g1, setup->h2, setup->gtr, setup->fr);
        new_proof->ipa_proof = dummy_proof;
    }
    else
    {
        F *chunk_i_in_bits = new F[_log_n_chunks];
        int_to_Fvec(chunk_i_in_bits, chunk_i, _log_n_chunks);
        new_proof->ipa_proof = setup->gipp->generate_proof_k(chunks_kcom->row_coms, chunk_i_in_bits, F_ONE, _n_chunks, true);
    }
    new_proof->row_proof = chunk_provers[chunk_i]->prove_row(row_i, dummy);
    return new_proof;
}

// h^{i_{j,l}} can be easily computed, because

RowAux_v2 *Prover_v2::generate_aux_for_rows(int *rows, int row_n)
{
    RowAux_v2 *aux = new RowAux_v2;
    aux->row_n = row_n;
    aux->log_chunk_size = _log_chunk_size;
    aux->rows = rows; // shallow copy of rows.
    aux->chunk_is = new int[row_n];
    aux->row_is = new int[row_n];
    for (int j = 0; j < row_n; j++)
    {
        aux->chunk_is[j] = rows[j] / _chunk_size;
        aux->row_is[j] = rows[j] % _chunk_size;
    }

    aux->idx_com = new G1[_log_table_row];

    aux->idx = new F *[_log_table_row];
    aux->hidx = new G2 *[_log_table_row];
    aux->h_tmi = new G2 *[_log_chunk_size];
    for (int l = 0; l < _log_table_row; l++)
    {
        aux->idx[l] = new F[row_n];
        aux->hidx[l] = new G2[row_n];
        if (l >= _log_n_chunks)
        {
            aux->h_tmi[l - _log_n_chunks] = new G2[row_n];
        }
        for (int j = 0; j < row_n; j++)
        {
            aux->idx[l][j] = (aux->row_is[j] >> (_log_table_row - 1 - l)) & 1;
            if (aux->idx[l][j] == F_ZERO)
                    aux->hidx[l][j] = setup->G2_zero;
            else
                    aux->hidx[l][j] = setup->h2;
           
        }
        if (l >= _log_n_chunks)
        {
            G2 tmp_val = setup->h2tvec[l - _log_n_chunks] - setup->h2;
            for (int k = 0; k < row_n; k++)
            {
                if (aux->idx[l][k] == F_ONE)
                {
                    aux->h_tmi[l - _log_n_chunks][k] = tmp_val;
                }
                else
                {
                    aux->h_tmi[l - _log_n_chunks][k] = setup->h2tvec[l - _log_n_chunks];
                }
            }
        }
        aux->idx_com[l] = ip_F_G1(aux->idx[l], setup->gipp->ck_g1, row_n);
    }
    return aux;
}

MiniMultiRowProof_v2 *Prover_v2::_mini_prove_rows(RowAux_v2 *aux, Kopis_com<G1> *rows_kcom, bool dummy)
{
    MiniMultiRowProof_v2 *proof = new MiniMultiRowProof_v2;
    if (dummy)
    {
        proof->log_chunk_size = _log_chunk_size;
        int log_size = int(ceil(log2(aux->row_n)));
        proof->C_q = new GT[_log_chunk_size];
        proof->ip_qh = new GT[_log_chunk_size];
        for (int i = 0; i < _log_chunk_size; i++)
        {
            proof->C_q[i] = setup->gtr;
            proof->ip_qh[i] = setup->gtr;
        }

        proof->q_batched_tipp_proof = new BatchedTIPP_Proof;
        set_dummy_batched_tipp_proof(proof->q_batched_tipp_proof, _log_chunk_size, log_size, setup->g1, setup->h2, setup->gtr, setup->fr);
        proof->cf_mipp_proof = new MIPP_Proof_k;
        set_dummy_mipp_proof_k(proof->cf_mipp_proof, log_size, setup->g1, setup->h2, setup->gtr, setup->fr);
        proof->chunks_mipp_proof = new MIPP_Proof;
        set_dummy_mipp_proof(proof->chunks_mipp_proof, _log_chunk_size, setup->g1, setup->h2, setup->gtr, setup->fr);
        proof->chunk_ssq_com = setup->g1;
        return proof;
    }

    int row_n = aux->row_n;
    int *rows = aux->rows;
    int *chunk_is = aux->chunk_is;
    int *row_is = aux->row_is;

    proof->log_chunk_size = _log_chunk_size;
    proof->rows_kopis_com = rows_kcom->com;
    G1 *sub_row_coms = rows_kcom->row_coms;
    RowProof **row_proofs = new RowProof *[row_n];
    G1 **q_table = new G1 *[_log_chunk_size];
    for (int j = 0; j < row_n; j++)
    {
        row_proofs[j] = chunk_provers[chunk_is[j]]->prove_row(row_is[j]);
    }

    proof->C_q = new GT[_log_chunk_size];

    for (int l = 0; l < _log_chunk_size; l++)
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
    proof->ip_qh = new GT[_log_chunk_size];
    G1 *q_s_tmp = new G1[row_n];
    //
    BatchTIPP_Aux tipp_aux;
    tipp_aux.z = proof->ip_qh; // reference. should not delete.
    if (row_n >= 2)
    {
        tipp_aux.zL_0 = new GT[_log_chunk_size];
        tipp_aux.zR_0 = new GT[_log_chunk_size];
    }
    else
    {
        tipp_aux.zL_0 = nullptr;
        tipp_aux.zR_0 = nullptr;
    }
    for (int l = 0; l < _log_chunk_size; l++)
    {
        G1vec_s_power(q_s_tmp, q_table[l], proof->rand_s * proof->rand_s, row_n);
        // proof->ip_qh[l] = ip_G1_G2(q_s_tmp, aux->h_tmi[l], row_n);
        G1 sum_1 = setup->G1_zero;
        G1 sum_2 = setup->G1_zero;
        G1 sum_1_zL = setup->G1_zero;
        G1 sum_2_zL = setup->G1_zero;
        G1 sum_1_zR = setup->G1_zero;
        G1 sum_2_zR = setup->G1_zero;
        for (int j = 0; j < row_n; j++)
        {
            sum_1 += q_s_tmp[j];
            if (aux->idx[l+_log_n_chunks][j] == F_ONE)
                sum_2 += q_s_tmp[j];
            if (row_n >= 2)
            {
                if (j < row_n / 2)
                {
                    sum_1_zL += q_s_tmp[j + row_n / 2];
                    if (aux->idx[l+_log_n_chunks][j] == F_ONE)
                        sum_2_zL += q_s_tmp[j + row_n / 2];
                }
                else
                {
                    sum_1_zR += q_s_tmp[j - row_n / 2];
                    if (aux->idx[l+_log_n_chunks][j] == F_ONE)
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

    proof->q_batched_tipp_proof = setup->gipp->generate_proof_batched_tipp(q_table, aux->h_tmi, proof->rand_s, row_n, _log_chunk_size, &tipp_aux);
    if (tipp_aux.zL_0 != nullptr)
    {
        delete[] tipp_aux.zL_0;
        delete[] tipp_aux.zR_0;
    }

    // delete q_table
    for (int i = 0; i < _log_chunk_size; i++)
        delete[] q_table[i];
    delete[] q_table;

    // MIPP

    proof->cf_mipp_proof = setup->gipp->generate_proof_k(sub_row_coms, &s_sq, F_ONE, row_n, false);

    F *chunk_ssq_by_rows = new F[_n_chunks];
    for (int j = 0; j < _n_chunks; j++)
    {
        chunk_ssq_by_rows[j] = F_ZERO;
    }
    F ssq_power = F_ONE;
    for (int j = 0; j < row_n; j++)
    {
        chunk_ssq_by_rows[chunk_is[j]] += ssq_power;
        ssq_power *= s_sq;
    }
    proof->chunk_ssq_com = ip_F_G1(chunk_ssq_by_rows, setup->gipp->ck_g1, _n_chunks);
    proof->chunks_mipp_proof = setup->gipp->generate_proof(chunks_kcom->row_coms, chunk_ssq_by_rows, F_ONE, _n_chunks);
    //  show that chunk_ssq_by_rows is correct.
    delete[] chunk_ssq_by_rows;

    return proof;
}

MultiRowProof_v2 *Prover_v2::prove_rows(int *rows, int row_n, G1 *sub_row_coms, bool dummy)
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
    high_resolution_clock::time_point t1, t2;
    MultiRowProof_v2 *proof = new MultiRowProof_v2; // to delete somewhere
    if (dummy)
    {
        proof->row_n = row_n;
        proof->log_chunk_size = _log_chunk_size;
        int log_size = int(ceil(log2(row_n)));
        proof->idx_com = new G1[_log_n_chunks + _log_chunk_size];
        proof->C_q = new GT[_log_chunk_size];
        proof->ip_qh = new GT[_log_chunk_size];
        for (int i = 0; i < _log_n_chunks + _log_chunk_size; i++)
        {
            proof->idx_com[i] = setup->g1;
        }
        for (int i = 0; i < _log_chunk_size; i++)
        {
            proof->C_q[i] = setup->gtr;
            proof->ip_qh[i] = setup->gtr;
        }

        proof->q_batched_tipp_proof = new BatchedTIPP_Proof;
        set_dummy_batched_tipp_proof(proof->q_batched_tipp_proof, _log_chunk_size, log_size, setup->g1, setup->h2, setup->gtr, setup->fr);

        proof->q_batched_ipa_proof = new BatchedIPA_Proof;
        set_dummy_batched_ipa_proof(proof->q_batched_ipa_proof, _log_chunk_size, log_size, setup->g1, setup->h2, setup->gtr, setup->fr);

        proof->cf_mipp_proof = new MIPP_Proof_k;
        set_dummy_mipp_proof_k(proof->cf_mipp_proof, log_size, setup->g1, setup->h2, setup->gtr, setup->fr);

        return proof;
    }
    t1 = high_resolution_clock::now();
    int *chunk_is = new int[row_n];
    int *row_is = new int[row_n];
    int log_size = int(ceil(log2(row_n)));
    for (int j = 0; j < row_n; j++)
    {
        chunk_is[j] = rows[j] / _chunk_size;
        row_is[j] = rows[j] % _chunk_size;
    }
    proof->row_n = row_n;
    proof->log_chunk_size = _log_chunk_size;
    RowProof **row_proofs = new RowProof *[row_n];
    F **idx = new F *[_log_table_row];

    G2 **h_idx = new G2 *[_log_chunk_size];
    proof->idx_com = new G1[_log_table_row];
    G1 **q_table = new G1 *[_log_chunk_size];
    for (int j = 0; j < _log_table_row; j++)
    {
        idx[j] = new F[row_n];
        proof->idx_com[j] = setup->G1_zero;
    }
    for (int l = 0; l < _log_chunk_size; l++)
    {
        h_idx[l] = new G2[row_n];
        q_table[l] = new G1[row_n];
    }
    proof->C_q = new GT[_log_chunk_size];
    t2 = high_resolution_clock::now();
    cout << "init data for prove_rows time: " << get_time(t1, t2) << " seconds" << endl;

    //  Round 1 | step (1) & (2) | P -> V:  c_pi
    t1 = high_resolution_clock::now();
    for (int j = 0; j < row_n; j++)
    {
        for (int l = 0; l < _log_table_row; l++)
        {
            idx[l][j] = (rows[j] >> (_log_table_row - 1 - l)) & 1;
        }
    }

    for (int l = 0; l < _log_table_row; l++)
    {
        for (int j = 0; j < row_n; j++)
        {
            if (idx[l][j] == F_ZERO)
            {
                if (l >= _log_n_chunks)
                    h_idx[l - _log_n_chunks][j] = setup->G2_zero;
            }
            else
            {
                if (l >= _log_n_chunks)
                    h_idx[l - _log_n_chunks][j] = setup->h2;
                proof->idx_com[l] += setup->gipp->ck_g1[j];
            }
        }
    }
    t2 = high_resolution_clock::now();
    cout << "compute idx_com time: " << get_time(t1, t2) << " seconds" << endl;

    t1 = high_resolution_clock::now();
    for (int j = 0; j < row_n; j++)
    {
        sub_row_coms[j] = this->chunk_provers[chunk_is[j]]->row_coms[row_is[j]];
        row_proofs[j] = this->chunk_provers[chunk_is[j]]->prove_row(row_is[j]);
        for (int l = 0; l < _log_chunk_size; l++)
        {
            q_table[l][j] = row_proofs[j]->qs[l]; // note that q in code = \pi in paper
        }
    }
    t2 = high_resolution_clock::now();
    cout << "compute row_proofs time: " << get_time(t1, t2) << " seconds" << endl;

    // delete row proofs
    for (int i = 0; i < row_n; i++)
        delete row_proofs[i];
    delete[] row_proofs;

    t1 = high_resolution_clock::now();
    for (int l = 0; l < _log_chunk_size; l++)
    {
        proof->C_q[l] = ip_G1_G2(q_table[l], setup->gipp->ck_h2, row_n); // In paper: C_pi[l]
    }
    t2 = high_resolution_clock::now();
    cout << "compute C_q time: " << get_time(t1, t2) << " seconds" << endl;

    // Round 2 | step(3) | V -> P: send random s

    proof->rand_s = non_zero_rand();

    // h^{t_l - i_{j,l}}
    G2 **h_tmi = new G2 *[_log_chunk_size];
    for (int j = 0; j < _log_chunk_size; j++)
    {
        h_tmi[j] = new G2[row_n];
    }
    proof->ip_qh = new GT[_log_chunk_size]; // inner product of q and h^{t-i} with rand_s power

    G1 *q_s_tmp = new G1[row_n];

    t1 = high_resolution_clock::now();
    BatchTIPP_Aux tipp_aux;
    tipp_aux.z = proof->ip_qh;
    if (row_n >= 2)
    {
        tipp_aux.zL_0 = new GT[_log_chunk_size];
        tipp_aux.zR_0 = new GT[_log_chunk_size];
    }
    else
    {
        tipp_aux.zL_0 = nullptr;
        tipp_aux.zR_0 = nullptr;
    }
    for (int l = 0; l < _log_chunk_size; l++)
    {
        G2 tmp_val = setup->h2tvec[l] - setup->h2;
        for (int k = 0; k < row_n; k++)
        {
            if (idx[l+_log_n_chunks][k] == F_ZERO)
            {
                h_tmi[l][k] = setup->h2tvec[l];
            }
            else
            {
                h_tmi[l][k] = tmp_val;
            }
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
            if (idx[l + _log_n_chunks][j] == F_ONE)
                sum_2 += q_s_tmp[j];
            if (row_n >= 2)
            {
                if (j < row_n / 2)
                {
                    sum_1_zL += q_s_tmp[j + row_n / 2];
                    if (idx[l + _log_n_chunks][j] == F_ONE)
                        sum_2_zL += q_s_tmp[j + row_n / 2];
                }
                else
                {
                    sum_1_zR += q_s_tmp[j - row_n / 2];
                    if (idx[l + _log_n_chunks][j] == F_ONE)
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
    t2 = high_resolution_clock::now();
    cout << "compute ip_qh and tipp_aux time: " << get_time(t1, t2) << " seconds" << endl;
    delete[] q_s_tmp;

    // delete h_idx
    for (int j = 0; j < _log_chunk_size; j++)
    {
        delete[] h_idx[j];
    }
    delete[] h_idx;

    t1 = high_resolution_clock::now();
    proof->rows_kopis_com = ip_G1_G2(sub_row_coms, setup->gipp->ck_h2, row_n); // C_F
    F *sq_powers = new F[row_n];
    t2 = high_resolution_clock::now();
    cout << "compute rows_kopis_com time: " << get_time(t1, t2) << " seconds" << endl;
    t1 = high_resolution_clock::now();
    s_powers(sq_powers, proof->rand_s * proof->rand_s, row_n);
    proof->rows_com_rlc = ip_F_G1(sq_powers, sub_row_coms, row_n); // Step 4(1) C_aggr
    delete[] sq_powers;
    t2 = high_resolution_clock::now();
    cout << "compute rows_com_rlc time: " << get_time(t1, t2) << " seconds" << endl;

    // Round 3 | P->V | send poly_t_rlc and ip_qh to V
    // Large Round 4 run l TIPPs | Step 5
    t1 = high_resolution_clock::now();
    proof->q_batched_tipp_proof = setup->gipp->generate_proof_batched_tipp(q_table, h_tmi, proof->rand_s, row_n, _log_chunk_size, &tipp_aux);
    t2 = high_resolution_clock::now();
    cout << "compute q_batched_tipp_proof time: " << get_time(t1, t2) << " seconds" << endl;

    if (tipp_aux.zL_0 != nullptr)
    {
        delete[] tipp_aux.zL_0;
        delete[] tipp_aux.zR_0;
    }
    // delete h_tmi not used anymore
    for (int j = 0; j < _log_chunk_size; j++)
        delete h_tmi[j];
    delete[] h_tmi;

    // delete q_table
    for (int j = 0; j < _log_chunk_size; j++)
    {
        delete[] q_table[j];
    }
    delete[] q_table;

    // Large Round 4 run MIPP
    t1 = high_resolution_clock::now();
    F s_sq = proof->rand_s * proof->rand_s;
    proof->cf_mipp_proof = setup->gipp->generate_proof_k(sub_row_coms, &s_sq, F_ONE, row_n, false);
    t2 = high_resolution_clock::now();
    cout << "compute cf_mipp_proof time: " << get_time(t1, t2) << " seconds" << endl;

    t1 = high_resolution_clock::now();
    F *chunk_ssq_by_rows = new F[_n_chunks];
    for (int j = 0; j < _n_chunks; j++)
    {
        chunk_ssq_by_rows[j] = F_ZERO;
    }
    F ssq_power = F_ONE;
    for (int j = 0; j < row_n; j++)
    {
        chunk_ssq_by_rows[chunk_is[j]] += ssq_power;
        ssq_power *= s_sq;
    }
    t2 = high_resolution_clock::now();
    cout << "compute chunk_ssq_by_rows time: " << get_time(t1, t2) << " seconds" << endl;
    t1 = high_resolution_clock::now();
    proof->chunk_ssq_com = ip_F_G1(chunk_ssq_by_rows, setup->gipp->ck_g1, _n_chunks);
    proof->chunks_mipp_proof = setup->gipp->generate_proof(chunks_kcom->row_coms, chunk_ssq_by_rows, F_ONE, _n_chunks);
    t2 = high_resolution_clock::now();
    cout << "compute chunks_mipp_proof time: " << get_time(t1, t2) << " seconds" << endl;

    //  show that chunk_ssq_by_rows is correct.
    delete[] chunk_ssq_by_rows;

    // Step 6 only in verifier.
    // Round 5 | V->P | another randomness, log_size | Step 7
    

    proof->rand_s_i = non_zero_rand();
    

    t1 = high_resolution_clock::now();
    F **cons1 = new F *[_log_table_row];
    for (int l = 0; l < _log_table_row; l++)
    {
        cons1[l] = new F[row_n];
        for (int j = 0; j < row_n; j++)
        {
            cons1[l][j] = 1 - idx[l][j];
        }
    }
    t2 = high_resolution_clock::now();
    cout << "compute cons1 time: " << get_time(t1, t2) << " seconds" << endl;
    t1 = high_resolution_clock::now();
    proof->q_batched_ipa_proof = setup->gipp->generate_proof_batched_ipa(idx, cons1, proof->rand_s_i, row_n, _log_table_row);
    t2 = high_resolution_clock::now();
    cout << "compute q_batched_ipa_proof time: " << get_time(t1, t2) << " seconds" << endl;

    for (int l = 0; l < _log_table_row; l++)
    {
        delete[] cons1[l];
        delete[] idx[l];
    }
    delete[] cons1;
    delete[] idx;

    return proof;
}

void Prover_v2::update_row(int row, F *row_data, int data_col, G1 *row_com, bool dummy)
{
    if (dummy)
        return;
    int chunk_i = row / _chunk_size;
    int row_i = row % _chunk_size;
    this->chunk_provers[chunk_i]->update_row(row_i, row_data, data_col, row_com, dummy);
    // also update local fields: chunks_kcom.
    chunks_kcom->com *= my_loop(chunk_provers[chunk_i]->table_com - chunks_kcom->row_coms[chunk_i], setup->gipp->ck_h2[chunk_i]);
    chunks_kcom->row_coms[chunk_i] = this->chunk_provers[chunk_i]->table_com;
}

UpdateRowsProof_New_v2 *Prover_v2::update_rows_new(int *rows, F **new_data, int row_n, bool dummy)
{

    high_resolution_clock::time_point t1, t2, t3;
    UpdateRowsProof_New_v2 *proof = new UpdateRowsProof_New_v2;
    int log_k = int(ceil(log2(row_n)));

    int *chunk_is = new int[row_n];
    int *row_is = new int[row_n];
    for (int j = 0; j < row_n; j++)
    {
        chunk_is[j] = rows[j] / _chunk_size;
        row_is[j] = rows[j] % _chunk_size;
    }

    // Step 0: idx related
    t1 = high_resolution_clock::now();
    RowAux_v2 *aux = generate_aux_for_rows(rows, row_n);
    proof->idx = aux->idx;
    proof->idx_com = aux->idx_com;
    t2 = high_resolution_clock::now();
    cout << "Time for generating aux: " << get_time(t1, t2) << " seconds" << endl;

    t1 = high_resolution_clock::now();

    proof->idx_kcom = new Kopis_com<G2> *[_log_table_row]; // hidx[l] = idx_kcom[l].row_coms
    for (int l = 0; l < _log_table_row; l++)
    {
        proof->idx_kcom[l] = new Kopis_com<G2>;
        proof->idx_kcom[l]->com = my_loop(aux->idx_com[l], setup->kopis_g2->kzg->h);
        proof->idx_kcom[l]->row_coms = aux->hidx[l];
        proof->idx_kcom[l]->size = row_n;
    }
    t2 = high_resolution_clock::now();
    cout << "Time for generating idx_kcom: " << get_time(t1, t2) << " seconds" << endl;
    proof->row_n = row_n;
    proof->log_chunk_size = _log_chunk_size;

    // Round1 - Step1

    t1 = high_resolution_clock::now();
    F **old_data_ptr = new F *[row_n];
    for (int j = 0; j < row_n; j++)
    {
        old_data_ptr[j] = new F[setup->_max_col];
        memcpy(old_data_ptr[j], chunk_provers[chunk_is[j]]->_data[row_is[j]], setup->_max_col * sizeof(F));
    }
    G1 *old_sub_row_coms = new G1[row_n];
    for (int j = 0; j < row_n; j++)
    {
        old_sub_row_coms[j] = chunk_provers[chunk_is[j]]->row_coms[row_is[j]];
    }

    proof->old_F_kopis_com = setup->kopis->commit(old_data_ptr, row_n, setup->_log_col, setup->_max_col, old_sub_row_coms); // avoid computing row com again.
    delete[] old_sub_row_coms;
    t2 = high_resolution_clock::now();
    cout << "Time for computing old_F_kopis_com (reuse row_coms): " << get_time(t1, t2) << " seconds" << endl;
    t1 = high_resolution_clock::now();
    proof->new_F_kopis_com = setup->kopis->commit(new_data, row_n, setup->_log_col, setup->_max_col); // here computs row com already, avoid computing row com in update
    t2 = high_resolution_clock::now();
    cout << "Time for computing new_F_kopis_com: " << get_time(t1, t2) << " seconds" << endl;
    // save data of old F

    // Step 2

    t1 = high_resolution_clock::now();
    proof->old_proof = _mini_prove_rows(aux, proof->old_F_kopis_com, dummy);
    t2 = high_resolution_clock::now();
    cout << "Time for computing old_lookup_proof: " << get_time(t1, t2) << " seconds" << endl;
    G1 *old_row_beta_coms = new G1[row_n];
    for (int j = 0; j < row_n; j++)
    {
        old_row_beta_coms[j] = chunk_provers[chunk_is[j]]->row_beta_coms[row_is[j]];
    }

    t1 = high_resolution_clock::now();
    // Step 3 update aux
    for (int i = 0; i < row_n; i++)
    {
        update_row(rows[i], new_data[i], setup->_max_col, &proof->new_F_kopis_com->row_coms[i], dummy);
    }
    t2 = high_resolution_clock::now();
    cout << "Time for updating rows: " << get_time(t1, t2) << " seconds" << endl;
    // Step 4
    t1 = high_resolution_clock::now();
    proof->new_proof = _mini_prove_rows(aux, proof->new_F_kopis_com, dummy);
    t2 = high_resolution_clock::now();
    cout << "Time for computing new_lookup_proof: " << get_time(t1, t2) << " seconds" << endl;
    // Step 5

    // Step 6: P->V send C_old_delta and C_new_delta

    // init timer

    t1 = high_resolution_clock::now();
    int *nrow_in_chunk = new int[_n_chunks];
    int non_zero_chunks = 0;
    for (int j = 0; j < _n_chunks; j++)
    {
        nrow_in_chunk[j] = 0;
    }
    for (int j = 0; j < row_n; j++)
    {
        if (nrow_in_chunk[chunk_is[j]] == 0)
            non_zero_chunks++;
        nrow_in_chunk[chunk_is[j]]++;
    }

    G1 *old_delta_com_in_chunk = new G1[_n_chunks];
    G1 *new_delta_com_in_chunk = new G1[_n_chunks];
    for (int j = 0; j < _n_chunks; j++)
    {
        old_delta_com_in_chunk[j] = setup->G1_zero;
        new_delta_com_in_chunk[j] = setup->G1_zero;
    }
    for (int j = 0; j < row_n; j++)
    {
        old_delta_com_in_chunk[chunk_is[j]] += old_row_beta_coms[j];
        new_delta_com_in_chunk[chunk_is[j]] += chunk_provers[chunk_is[j]]->row_beta_coms[row_is[j]];
    }
    // now compute the contribution to chunks.
    // use mulvec of subset
    G1 *old_delta_com_in_chunk_nonzero = new G1[non_zero_chunks];
    G1 *new_delta_com_in_chunk_nonzero = new G1[non_zero_chunks];
    G2 *ck_nonzero = new G2[non_zero_chunks];
    int k = 0;
    for (int j = 0; j < _n_chunks; j++)
    {
        if (nrow_in_chunk[j] > 0)
        {
            old_delta_com_in_chunk_nonzero[k] = old_delta_com_in_chunk[j];
            new_delta_com_in_chunk_nonzero[k] = new_delta_com_in_chunk[j];
            ck_nonzero[k] = setup->gipp->ck_h2[j];
            k++;
        }
    }
    proof->old_delta_com = ip_G1_G2(old_delta_com_in_chunk_nonzero, ck_nonzero, non_zero_chunks);
    proof->new_delta_com = ip_G1_G2(new_delta_com_in_chunk_nonzero, ck_nonzero, non_zero_chunks);
    t2 = high_resolution_clock::now();
    cout << "Time for computing 2 delta_coms: " << get_time(t1, t2) << " seconds" << endl;
    delete[] old_delta_com_in_chunk_nonzero;
    delete[] new_delta_com_in_chunk_nonzero;
    delete[] ck_nonzero;

    delete[] nrow_in_chunk;
    delete[] old_row_beta_coms;

    // Step 7: P->V send r1, r2,
    proof->r1 = new F[_log_n_chunks + _log_chunk_size + setup->_log_col];
    for (int i = 0; i < _log_n_chunks + _log_chunk_size + setup->_log_col; i++)
        proof->r1[i] = F(rand());
    proof->r2 = proof->r1 + _log_n_chunks + _log_chunk_size;
    F *row_r1 = proof->r1 + _log_n_chunks;

    // Step 8: P->V y_old_delta, y_new_delta, y_old_proof, y_new_proof
    // open delta(x, y) \sum_{j\in rows} beta(x, j) f_j(y) at point (r1, r2)

    // 8.1 compute old_delta_val
    t1 = high_resolution_clock::now();
    proof->old_delta_r1_r2_open = new Kopis_open;
    proof->old_delta_r1_r2_open->col_dim = _log_chunk_size + setup->_log_col;
    proof->old_delta_r1_r2_open->ipa_proof = setup->gipp->generate_proof_k(old_delta_com_in_chunk, proof->r1, F_ONE, _n_chunks, true);

    // the old_delta_poly:
    F *old_delta_poly = new F[1 << (_log_chunk_size + setup->_log_col)];
    // init to 0
    for (int i = 0; i < (1 << (_log_chunk_size + setup->_log_col)); i++)
        old_delta_poly[i] = F_ZERO;
    for (int j = 0; j < row_n; j++)
    {
        for (int icol = 0; icol < setup->_max_col; icol++)
        {
            old_delta_poly[row_is[j] * setup->_max_col + icol] += old_data_ptr[j][icol] * beta(proof->r1, chunk_is[j], _log_n_chunks);
        }
    }

    proof->old_delta_r1_r2_open->val = multi_eval(old_delta_poly, row_r1, _log_chunk_size + setup->_log_col, _chunk_size * setup->_max_col);
    proof->old_delta_r1_r2_open->kzg_proof = new G1[_log_chunk_size + setup->_log_col];
    multi_Q_of_f(proof->old_delta_r1_r2_open->kzg_proof, old_delta_poly, row_r1, _log_chunk_size + setup->_log_col, setup->g1tvec_tower_all, setup->g1, 1);
    t2 = high_resolution_clock::now();
    cout << "Time for computing old_delta_poly: " << get_time(t1, t2) << " seconds" << endl;

    delete[] old_delta_poly;
    // delete temp old subtable
    for (int j = 0; j < row_n; j++)
    {
        delete[] old_data_ptr[j];
    }
    delete[] old_data_ptr;
    delete[] old_delta_com_in_chunk;

    // compute new delta val, and proof
    t1 = high_resolution_clock::now();
    proof->new_delta_r1_r2_open = new Kopis_open;
    proof->new_delta_r1_r2_open->col_dim = _log_chunk_size + setup->_log_col;
    proof->new_delta_r1_r2_open->ipa_proof = setup->gipp->generate_proof_k(new_delta_com_in_chunk, proof->r1, F_ONE, _n_chunks, true);

    // the new_delta_poly:
    F *new_delta_poly = new F[1 << (_log_chunk_size + setup->_log_col)];
    // init to 0
    for (int i = 0; i < (1 << (_log_chunk_size + setup->_log_col)); i++)
        new_delta_poly[i] = F_ZERO;
    for (int j = 0; j < row_n; j++)
    {
        for (int icol = 0; icol < setup->_max_col; icol++)
        {
            new_delta_poly[row_is[j] * setup->_max_col + icol] += new_data[j][icol] * beta(proof->r1, chunk_is[j], _log_n_chunks);
        }
    }

    proof->new_delta_r1_r2_open->val = multi_eval(new_delta_poly, row_r1, _log_chunk_size + setup->_log_col, _chunk_size * setup->_max_col);
    proof->new_delta_r1_r2_open->kzg_proof = new G1[_log_chunk_size + setup->_log_col];
    multi_Q_of_f(proof->new_delta_r1_r2_open->kzg_proof, new_delta_poly, row_r1, _log_chunk_size + setup->_log_col, setup->g1tvec_tower_all, setup->g1, 1);
    t2 = high_resolution_clock::now();
    cout << "Time for computing new_delta_poly: " << get_time(t1, t2) << " seconds" << endl;

    delete[] new_delta_poly;

    delete[] new_delta_com_in_chunk;

    // step 9. CP-SNARK

    delete aux;
    return proof;
}

UpdateRowsProof_NewNew_v2 *Prover_v2::update_rows_newnew(int *rows, F **new_data, int row_n, bool dummy)
{

    high_resolution_clock::time_point t1, t2, t3;
    UpdateRowsProof_NewNew_v2 *proof = new UpdateRowsProof_NewNew_v2;
    int log_k = int(ceil(log2(row_n)));

    int *chunk_is = new int[row_n];
    int *row_is = new int[row_n];
    for (int j = 0; j < row_n; j++)
    {
        chunk_is[j] = rows[j] / _chunk_size;
        row_is[j] = rows[j] % _chunk_size;
    }

    // Step 0: idx related
    t1 = high_resolution_clock::now();
    RowAux_v2 *aux = generate_aux_for_rows(rows, row_n);
    proof->idx = aux->idx;
    proof->idx_com = aux->idx_com;
    t2 = high_resolution_clock::now();
    cout << "Time for generating aux: " << get_time(t1, t2) << " seconds" << endl;

    t1 = high_resolution_clock::now();

    proof->idx_kcom = new Kopis_com<G2> *[_log_table_row]; // hidx[l] = idx_kcom[l].row_coms
    for (int l = 0; l < _log_table_row; l++)
    {
        proof->idx_kcom[l] = new Kopis_com<G2>;
        proof->idx_kcom[l]->com = my_loop(aux->idx_com[l], setup->kopis_g2->kzg->h);
        proof->idx_kcom[l]->row_coms = aux->hidx[l];
        proof->idx_kcom[l]->size = row_n;
    }
    t2 = high_resolution_clock::now();
    cout << "Time for generating idx_kcom: " << get_time(t1, t2) << " seconds" << endl;
    proof->row_n = row_n;
    proof->log_chunk_size = _log_chunk_size;

    // Round1 - Step1

    t1 = high_resolution_clock::now();
    F **old_data_ptr = new F *[row_n];
    for (int j = 0; j < row_n; j++)
    {
        old_data_ptr[j] = new F[setup->_max_col];
        memcpy(old_data_ptr[j], chunk_provers[chunk_is[j]]->_data[row_is[j]], setup->_max_col * sizeof(F));
    }
    G1 *old_sub_row_coms = new G1[row_n];
    for (int j = 0; j < row_n; j++)
    {
        old_sub_row_coms[j] = chunk_provers[chunk_is[j]]->row_coms[row_is[j]];
    }

    proof->old_F_kopis_com = setup->kopis->commit(old_data_ptr, row_n, setup->_log_col, setup->_max_col, old_sub_row_coms); // avoid computing row com again.
    delete[] old_sub_row_coms;
    t2 = high_resolution_clock::now();
    cout << "Time for computing old_F_kopis_com (reuse row_coms): " << get_time(t1, t2) << " seconds" << endl;
    t1 = high_resolution_clock::now();
    proof->new_F_kopis_com = setup->kopis->commit(new_data, row_n, setup->_log_col, setup->_max_col); // here computs row com already, avoid computing row com in update
    t2 = high_resolution_clock::now();
    cout << "Time for computing new_F_kopis_com: " << get_time(t1, t2) << " seconds" << endl;
    // save data of old F

    // Step 2
    // V: send rand_lookup to merge two lookup proves:
    // show that F + rand_lookup * F' = (T + rand_lookup * T')_{rows}
    proof->rand_lookup = F(rand());
    // what is needed: q, q' => tilde_{q}
    // C_f, C_f' => tilde_{C_f}
    // the same aux->htmi

    proof->lookup_proof = new MiniMultiRowProof_v2;
    GT::pow(proof->lookup_proof->rows_kopis_com, proof->new_F_kopis_com->com, proof->rand_lookup);
    proof->lookup_proof->rows_kopis_com = proof->lookup_proof->rows_kopis_com * proof->old_F_kopis_com->com;

    G1* tilde_chunk_coms = new G1[_n_chunks];
    for (int j = 0; j < _n_chunks; j++)
    {
        tilde_chunk_coms[j] = this->chunks_kcom->row_coms[j];
    }

    t1 = high_resolution_clock::now();
    // to construct q:
    G1 **q_table = new G1 *[_log_chunk_size];
    for (int l = 0; l < _log_chunk_size; l++)
    {
        q_table[l] = new G1[row_n];
    }
    RowProof *row_proof;
    for (int j = 0; j < row_n; j++)
    {
        row_proof = chunk_provers[chunk_is[j]]->prove_row(row_is[j], dummy);
        for (int l = 0; l < _log_chunk_size; l++)
        {
            q_table[l][j] = row_proof->qs[l]; // note that q in code = \pi in paper
        }
        delete row_proof;
    }
    t2 = high_resolution_clock::now();
    cout << "Time for computing q_table part1: " << get_time(t1, t2) << " seconds" << endl;
    t1 = high_resolution_clock::now();
    G1 *tilde_row_coms = new G1[row_n];
    memcpy(tilde_row_coms, proof->old_F_kopis_com->row_coms, row_n * sizeof(G1));
    for (int j = 0; j < row_n; j++)
    {
        tilde_row_coms[j] += proof->new_F_kopis_com->row_coms[j] * proof->rand_lookup;
    }
    t2 = high_resolution_clock::now();
    cout << "Time for computing tilde_row_coms: " << get_time(t1, t2) << " seconds" << endl;

    G1 *old_row_beta_coms = new G1[row_n];
    for (int j = 0; j < row_n; j++)
    {
        old_row_beta_coms[j] = chunk_provers[chunk_is[j]]->row_beta_coms[row_is[j]];
    }

    t1 = high_resolution_clock::now();
    // Step 3 update aux
    for (int i = 0; i < row_n; i++)
    {
        update_row(rows[i], new_data[i], setup->_max_col, &proof->new_F_kopis_com->row_coms[i], dummy);
    }
    t2 = high_resolution_clock::now();
    cout << "Time for updating rows: " << get_time(t1, t2) << " seconds" << endl;
    // Step 4

    t1 = high_resolution_clock::now();
    for (int j = 0; j < row_n; j++)
    {
        row_proof = chunk_provers[chunk_is[j]]->prove_row(row_is[j], dummy);
        for (int l = 0; l < _log_chunk_size; l++)
        {
            q_table[l][j] += row_proof->qs[l] * proof->rand_lookup; // note that q in code = \pi in paper
        }
        delete row_proof;
    }
    t2 = high_resolution_clock::now();
    cout << "Time for computing q_table part2: " << get_time(t1, t2) << " seconds" << endl;
    // now q_table is tilde{q} = q + r * q'
    t1 = high_resolution_clock::now();
    proof->lookup_proof->C_q = new GT[_log_chunk_size];
    for (int l = 0; l < _log_chunk_size; l++)
    {
        proof->lookup_proof->C_q[l] = ip_G1_G2(q_table[l], setup->gipp->ck_h2, row_n);
    }
    t2 = high_resolution_clock::now();
    cout << "Time for computing C_q: " << get_time(t1, t2) << " seconds" << endl;
    proof->lookup_proof->rand_s = non_zero_rand();
    // compute ip_qh and tipp_aux
    G1 *q_s_tmp = new G1[row_n];
    t1 = high_resolution_clock::now();
    proof->lookup_proof->ip_qh = new GT[_log_chunk_size];
    BatchTIPP_Aux tipp_aux;
    tipp_aux.z = proof->lookup_proof->ip_qh;
    if (row_n >= 2)
    {
        tipp_aux.zL_0 = new GT[_log_chunk_size];
        tipp_aux.zR_0 = new GT[_log_chunk_size];
    }
    else
    {
        tipp_aux.zL_0 = nullptr;
        tipp_aux.zR_0 = nullptr;
    }
    F rand_s = proof->lookup_proof->rand_s;
    F rand_s_sq = rand_s * rand_s;
    for (int l = 0; l < _log_chunk_size; l++)
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
            if (aux->idx[l+_log_n_chunks][j] == F_ONE)
                sum_2 += q_s_tmp[j];
            if (row_n >= 2)
            {
                if (j < row_n / 2)
                {
                    sum_1_zL += q_s_tmp[j + row_n / 2];
                    if (aux->idx[l+_log_n_chunks][j] == F_ONE)
                        sum_2_zL += q_s_tmp[j + row_n / 2];
                }
                else
                {
                    sum_1_zR += q_s_tmp[j - row_n / 2];
                    if (aux->idx[l+_log_n_chunks][j] == F_ONE)
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
    t2 = high_resolution_clock::now();
    cout << "Time for computing ip_qh and tipp_aux: " << get_time(t1, t2) << " seconds" << endl;

    t1 = high_resolution_clock::now();
    F *sq_powers = new F[row_n];
    s_powers(sq_powers, rand_s_sq, row_n);
    proof->lookup_proof->rows_com_rlc = ip_F_G1(sq_powers, tilde_row_coms, row_n);
    delete[] sq_powers;
    t2 = high_resolution_clock::now();
    cout << "Time for computing rows_com_rlc: " << get_time(t1, t2) << " seconds" << endl;

    t1 = high_resolution_clock::now();
    proof->lookup_proof->q_batched_tipp_proof = setup->gipp->generate_proof_batched_tipp(q_table, aux->h_tmi, proof->lookup_proof->rand_s, row_n, setup->_log_row, &tipp_aux);
    t2 = high_resolution_clock::now();
    cout << "Time for computing q_batched_tipp_proof: " << get_time(t1, t2) << " seconds" << endl;
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
    t1 = high_resolution_clock::now();
    proof->lookup_proof->cf_mipp_proof = setup->gipp->generate_proof_k(tilde_row_coms, &rand_s_sq, F_ONE, row_n, false);
    t2 = high_resolution_clock::now();
    cout << "Time for computing cf_mipp_proof: " << get_time(t1, t2) << " seconds" << endl;

    t1 = high_resolution_clock::now();
    F *chunk_ssq_by_rows = new F[_n_chunks];
    for (int j = 0; j < _n_chunks; j++)
    {
        chunk_ssq_by_rows[j] = F_ZERO;
    }
    F ssq_power = F_ONE;
    for (int j = 0; j < row_n; j++)
    {
        chunk_ssq_by_rows[chunk_is[j]] += ssq_power;
        ssq_power *= rand_s_sq;
    }
    for (int j = 0; j < _n_chunks; j++)
    {
        tilde_chunk_coms[j] += this->chunks_kcom->row_coms[j] * proof->rand_lookup;
    }
    t2 = high_resolution_clock::now();
    cout << "Time for computing chunk_ssq_by_rows: " << get_time(t1, t2) << " seconds" << endl;
    t1 = high_resolution_clock::now();
    proof->lookup_proof->chunk_ssq_com = ip_F_G1(chunk_ssq_by_rows, setup->gipp->ck_g1, _n_chunks);
    proof->lookup_proof->chunks_mipp_proof = setup->gipp->generate_proof(tilde_chunk_coms, chunk_ssq_by_rows, F_ONE, _n_chunks);
    //  show that chunk_ssq_by_rows is correct.
    delete[] chunk_ssq_by_rows;
    t2 = high_resolution_clock::now();
    cout << "Time for computing chunks_mipp_proof: " << get_time(t1, t2) << " seconds" << endl;

    // Step 5

    // Step 6: P->V send C_old_delta and C_new_delta

    // init timer

    t1 = high_resolution_clock::now();
    int *nrow_in_chunk = new int[_n_chunks];
    int non_zero_chunks = 0;
    for (int j = 0; j < _n_chunks; j++)
    {
        nrow_in_chunk[j] = 0;
    }
    for (int j = 0; j < row_n; j++)
    {
        if (nrow_in_chunk[chunk_is[j]] == 0)
            non_zero_chunks++;
        nrow_in_chunk[chunk_is[j]]++;
    }

    G1 *old_delta_com_in_chunk = new G1[_n_chunks];
    G1 *new_delta_com_in_chunk = new G1[_n_chunks];
    for (int j = 0; j < _n_chunks; j++)
    {
        old_delta_com_in_chunk[j] = setup->G1_zero;
        new_delta_com_in_chunk[j] = setup->G1_zero;
    }
    for (int j = 0; j < row_n; j++)
    {
        old_delta_com_in_chunk[chunk_is[j]] += old_row_beta_coms[j];
        new_delta_com_in_chunk[chunk_is[j]] += chunk_provers[chunk_is[j]]->row_beta_coms[row_is[j]];
    }
    // now compute the contribution to chunks.
    // use mulvec of subset
    G1 *old_delta_com_in_chunk_nonzero = new G1[non_zero_chunks];
    G1 *new_delta_com_in_chunk_nonzero = new G1[non_zero_chunks];
    G2 *ck_nonzero = new G2[non_zero_chunks];
    int k = 0;
    for (int j = 0; j < _n_chunks; j++)
    {
        if (nrow_in_chunk[j] > 0)
        {
            old_delta_com_in_chunk_nonzero[k] = old_delta_com_in_chunk[j];
            new_delta_com_in_chunk_nonzero[k] = new_delta_com_in_chunk[j];
            ck_nonzero[k] = setup->gipp->ck_h2[j];
            k++;
        }
    }
    proof->old_delta_com = ip_G1_G2(old_delta_com_in_chunk_nonzero, ck_nonzero, non_zero_chunks);
    proof->new_delta_com = ip_G1_G2(new_delta_com_in_chunk_nonzero, ck_nonzero, non_zero_chunks);
    t2 = high_resolution_clock::now();
    cout << "Time for computing 2 delta_coms: " << get_time(t1, t2) << " seconds" << endl;
    delete[] old_delta_com_in_chunk_nonzero;
    delete[] new_delta_com_in_chunk_nonzero;
    delete[] ck_nonzero;

    delete[] nrow_in_chunk;
    delete[] old_row_beta_coms;

    // Step 7: P->V send r1, r2,
    proof->r1 = new F[_log_n_chunks + _log_chunk_size + setup->_log_col];
    for (int i = 0; i < _log_n_chunks + _log_chunk_size + setup->_log_col; i++)
        proof->r1[i] = F(rand());
    proof->r2 = proof->r1 + _log_n_chunks + _log_chunk_size;
    F *row_r1 = proof->r1 + _log_n_chunks;

    // Step 8: P->V y_old_delta, y_new_delta, y_old_proof, y_new_proof
    // open delta(x, y) \sum_{j\in rows} beta(x, j) f_j(y) at point (r1, r2)

    // 8.1 compute old_delta_val
    t1 = high_resolution_clock::now();
    proof->old_delta_r1_r2_open = new Kopis_open;
    proof->old_delta_r1_r2_open->col_dim = _log_chunk_size + setup->_log_col;
    proof->old_delta_r1_r2_open->ipa_proof = setup->gipp->generate_proof_k(old_delta_com_in_chunk, proof->r1, F_ONE, _n_chunks, true);

    // the old_delta_poly:
    if (row_n >= _chunk_size)
    {
        F *old_delta_poly = new F[1 << (_log_chunk_size + setup->_log_col)];
        // init to 0
        for (int i = 0; i < (1 << (_log_chunk_size + setup->_log_col)); i++)
            old_delta_poly[i] = F_ZERO;
        for (int j = 0; j < row_n; j++)
        {
            for (int icol = 0; icol < setup->_max_col; icol++)
            {
                old_delta_poly[row_is[j] * setup->_max_col + icol] += old_data_ptr[j][icol] * beta(proof->r1, chunk_is[j], _log_n_chunks);
            }
        }

        proof->old_delta_r1_r2_open->val = multi_eval(old_delta_poly, row_r1, _log_chunk_size + setup->_log_col, _chunk_size * setup->_max_col);
        proof->old_delta_r1_r2_open->kzg_proof = new G1[_log_chunk_size + setup->_log_col];
        multi_Q_of_f(proof->old_delta_r1_r2_open->kzg_proof, old_delta_poly, row_r1, _log_chunk_size + setup->_log_col, setup->g1tvec_tower_all, setup->g1, 1);
        t2 = high_resolution_clock::now();
        cout << "Time for computing old_delta_poly (new method): " << get_time(t1, t2) << " seconds" << endl;

        delete[] old_delta_poly;

        cout << "new method for computing old_delta_poly" << endl;
    }
    else 
    {
        proof->old_delta_r1_r2_open->val = F_ZERO;
        proof->old_delta_r1_r2_open->kzg_proof = new G1[_log_chunk_size + setup->_log_col];
        for (int i = 0; i < _log_chunk_size + setup->_log_col; i++)
            proof->old_delta_r1_r2_open->kzg_proof[i] = setup->G1_zero;
        t1 = high_resolution_clock::now();
        G1 *qs = new G1[_log_chunk_size + setup->_log_col];
        for (int j = 0; j < row_n; j++)
        {
            proof->old_delta_r1_r2_open->val += multi_eval(old_data_ptr[j], proof->r2, setup->_log_col, setup->_max_col) * beta(proof->r1, rows[j], _log_n_chunks+_log_chunk_size);
            multi_Q_of_beta_rowi_f(qs, old_data_ptr[j], row_r1, row_is[j], _log_chunk_size, setup->_log_col, setup->g1tvec_tower_all, setup->g1);
            for (int l = 0; l < _log_chunk_size + setup->_log_col; l++)
            {
                proof->old_delta_r1_r2_open->kzg_proof[l] += qs[l] * beta(proof->r1, chunk_is[j], _log_n_chunks);
            }
        }
        t2 = high_resolution_clock::now();
        cout << "Time for computing old_delta_poly (old way): " << get_time(t1, t2) << " seconds" << endl;
        delete[] qs; 

        cout << "old method for computing old_delta_poly" << endl;
        
    }
    // delete temp old subtable
    for (int j = 0; j < row_n; j++)
    {
        delete[] old_data_ptr[j];
    }
    delete[] old_data_ptr;
    delete[] old_delta_com_in_chunk;

    // compute new delta val, and proof

    proof->new_delta_r1_r2_open = new Kopis_open;
    proof->new_delta_r1_r2_open->col_dim = _log_chunk_size + setup->_log_col;
    proof->new_delta_r1_r2_open->ipa_proof = setup->gipp->generate_proof_k(new_delta_com_in_chunk, proof->r1, F_ONE, _n_chunks, true);

    if (row_n >= _chunk_size)
    {
        // the new_delta_poly:
        t1 = high_resolution_clock::now();
        F *new_delta_poly = new F[1 << (_log_chunk_size + setup->_log_col)];
        // init to 0
        for (int i = 0; i < (1 << (_log_chunk_size + setup->_log_col)); i++)
            new_delta_poly[i] = F_ZERO;
        for (int j = 0; j < row_n; j++)
        {
            for (int icol = 0; icol < setup->_max_col; icol++)
            {
                new_delta_poly[row_is[j] * setup->_max_col + icol] += new_data[j][icol] * beta(proof->r1, chunk_is[j], _log_n_chunks);
            }
        }

        proof->new_delta_r1_r2_open->val = multi_eval(new_delta_poly, row_r1, _log_chunk_size + setup->_log_col, _chunk_size * setup->_max_col);
        proof->new_delta_r1_r2_open->kzg_proof = new G1[_log_chunk_size + setup->_log_col];
        multi_Q_of_f(proof->new_delta_r1_r2_open->kzg_proof, new_delta_poly, row_r1, _log_chunk_size + setup->_log_col, setup->g1tvec_tower_all, setup->g1, 1);
        t2 = high_resolution_clock::now();
        cout << "Time for computing new_delta_poly: " << get_time(t1, t2) << " seconds" << endl;
        delete[] new_delta_poly;
    }
    else
    {
        proof->new_delta_r1_r2_open->val = F_ZERO;
        proof->new_delta_r1_r2_open->kzg_proof = new G1[_log_chunk_size + setup->_log_col];
        for (int i = 0; i < _log_chunk_size + setup->_log_col; i++)
            proof->new_delta_r1_r2_open->kzg_proof[i] = setup->G1_zero;
        t1 = high_resolution_clock::now();
        G1 *qs = new G1[_log_chunk_size + setup->_log_col];
        for (int j = 0; j < row_n; j++)
        {
            proof->new_delta_r1_r2_open->val += multi_eval(new_data[j], proof->r2, setup->_log_col, setup->_max_col)* beta(proof->r1, rows[j], _log_n_chunks+_log_chunk_size);
            multi_Q_of_beta_rowi_f(qs, new_data[j], row_r1, row_is[j], _log_chunk_size, setup->_log_col, setup->g1tvec_tower_all, setup->g1);
            for (int l = 0; l < _log_chunk_size + setup->_log_col; l++)
            {
                proof->new_delta_r1_r2_open->kzg_proof[l] += qs[l] * beta(proof->r1, chunk_is[j], _log_n_chunks);
            }
        }
        t2 = high_resolution_clock::now();
        cout << "Time for computing new_delta_poly (old way): " << get_time(t1, t2) << " seconds" << endl;
        delete[] qs; 
    }

    delete[] new_delta_com_in_chunk;

    // step 9. CP-SNARK

    // delete aux
    delete aux;
    return proof;
}
