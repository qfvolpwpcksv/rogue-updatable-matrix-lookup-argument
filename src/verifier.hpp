#pragma once
#include "config_pc.hpp"

#include "prover.hpp"

class Verifier
{
public:
    Verifier(Setup *setup);
    ~Verifier();

    bool verify_row(const G1 &table_com, int row_i, RowProof *proof);
    bool verify_rows(const G1 &table_com, MultiRowProof *proof);

    bool verify_rows_mini(const G1 &table_com, MiniMultiRowProof *proof, int row_n, G1 *idx_com);

    bool verify_update_rows(const G1 &old_table_com, const G1 &new_table_com, UpdateRowsProof *proof);
    bool verify_update_rows_new(const G1 &old_table_com, const G1 &new_table_com, UpdateRowsProof_New *proof);
    bool verify_update_rows_newnew(const G1 &old_table_com, const G1 &new_table_com, UpdateRowsProof_NewNew *proof);

    Setup *setup;
    Prover *prover; // for debugging.
};
