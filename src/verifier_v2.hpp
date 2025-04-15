#pragma once
#include "config_pc.hpp"

#include "prover.hpp"
#include "prover_v2.hpp"

class Verifier_v2
{
public:
    Verifier_v2(Setup *setup, int n_chunks);
    ~Verifier_v2();

    bool verify_row(const Kopis_com<G1> &table_com, int row_i, RowProof_v2 *proof);
    bool verify_rows(const Kopis_com<G1> &table_com, MultiRowProof_v2 *proof); // should actually be commitment of idx

    bool verify_rows_mini(const Kopis_com<G1> &table_com, MiniMultiRowProof_v2 *proof, int row_n, G1 *idx_com);
    bool verify_update_rows_new(const Kopis_com<G1> &old_table_com, const Kopis_com<G1> &new_table_com, UpdateRowsProof_New_v2 *proof);
    bool verify_update_rows_newnew(const Kopis_com<G1> &old_table_com, const Kopis_com<G1> &new_table_com, UpdateRowsProof_NewNew_v2 *proof);
    Setup *setup;
    Prover_v2 *prover; // for debugging.

    int _n_chunks;
    int _log_n_chunks;
    int _chunk_size;
    int _log_chunk_size;
};