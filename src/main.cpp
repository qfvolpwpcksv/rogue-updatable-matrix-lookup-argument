#include "config_pc.hpp"
#include <mcl/bls12_381.hpp>
#include <fstream>
#include <iostream>
#include "ec.hpp"
#include "mimc.hpp"
#include "prover.hpp"
#include "prover_v2.hpp"
#include "verifier.hpp"
#include "verifier_v2.hpp"

using namespace mcl::bls12;

void init_large_data(F **data, int max_row, int max_col)
{
    for (int i = 0; i < max_row; i++)
    {
        data[i] = new F[max_col];
        for (int j = 0; j < max_col; j++)
        {
            data[i][j] = F(rand());
        }
    }
}

int main(int argc, char *argv[])
{
    initPairing(mcl::BLS12_381);
    elliptic_curves_init();
    init_hash();

    ifstream infile;
    ofstream outfile;

    if (argc < 3)
    {
        infile.open("../tests/input-ex.txt");
        outfile.open("../tests/output-ex.txt");
    }
    else
    {
        infile.open(argv[1]);
        outfile.open(argv[2]);
    }
    int max_row, max_col, n_chunks;
    int log_max_row, log_max_col, log_n_chunks;
    int row_n, update_row_n;
    F **data;

    infile >> log_max_row >> log_max_col >> log_n_chunks;
    cout << "log_max_row = " << log_max_row << " | " << "log_max_col = " << log_max_col << " | " << "log_n_chunks=" << log_n_chunks << endl;

    int lookup_exp_num;
    infile >> lookup_exp_num;
    int *lookup_row_ns;
    int *log_lookup_row_ns;
    if (lookup_exp_num >= 1)
    {
        cout << "lookup_exp_num = " << lookup_exp_num << endl;
        lookup_row_ns = new int[lookup_exp_num];
        log_lookup_row_ns = new int[lookup_exp_num];
        for (int i = 0; i < lookup_exp_num; i++)
        {
            infile >> log_lookup_row_ns[i];
            lookup_row_ns[i] = 1 << log_lookup_row_ns[i];
        }
    }

    int update_exp_num;
    infile >> update_exp_num;
    int *update_row_ns;
    int *log_update_row_ns;
    if (update_exp_num >= 1)
    {
        cout << "update_exp_num = " << update_exp_num << endl;
        update_row_ns = new int[update_exp_num];
        log_update_row_ns = new int[update_exp_num];
        for (int i = 0; i < update_exp_num; i++)
        {
            infile >> log_update_row_ns[i];
            update_row_ns[i] = 1 << log_update_row_ns[i];
        }
    }

    // 1 for dummy, 0 for non-dummy
    int setup_dummy;        // will make setup run in little time
    int prover_table_dummy; // will make prover::init() run in little time
    int row_prove_dummy;    // will make prover::prove_row() run in little time.
    int rows_prove_dummy;   // will make prover::prover_rows() and prover::_mini_prove_rows() run in little time. | note that this also affects update_rows() because it relies on _mini_prove_rows().

    infile >> setup_dummy >> prover_table_dummy >> row_prove_dummy >> rows_prove_dummy;

    infile.close();
    max_row = 1 << log_max_row;
    max_col = 1 << log_max_col;
    n_chunks = 1 << log_n_chunks; // Kopis representation of table if log_n_chunks = 0, n_chunks=1, then it is the same as not using kopis.

    cout << "max_row = " << max_row << endl;
    cout << "max_col = " << max_col << endl;
    cout << "n_chunks = " << n_chunks << endl;

    outfile << "max_row = " << max_row << endl;
    outfile << "max_col = " << max_col << endl;
    outfile << "n_chunks = " << n_chunks << endl;

    data = new F *[max_row];
    init_large_data(data, max_row, max_col);
    cout << "load data finished" << endl;

    high_resolution_clock::time_point t1, t2, t3;
    t1 = high_resolution_clock::now();
    Setup *setup = new Setup(max_row >> log_n_chunks, max_col, n_chunks, setup_dummy > 0);
    t2 = high_resolution_clock::now();
    cout << "setup complete in [" << get_time(t1, t2) << "] seconds" << endl;
    outfile << "setup of size (" << max_row << "/" << n_chunks << "x" << max_col << ") complete in [" << get_time(t1, t2) << "] seconds" << endl;

    if (n_chunks <= 1)
    {
        Prover *prover = new Prover(setup);
        cout << "prover created" << endl;
        t1 = high_resolution_clock::now();
        prover->init(data, max_row, max_col, prover_table_dummy > 0);
        t2 = high_resolution_clock::now();
        cout << "prover initialized" << endl;
        cout << "prover init complete in [" << get_time(t1, t2) << "] seconds" << endl;
        outfile << "prover of size (" << max_row << "x" << max_col << ") initialized in [" << get_time(t1, t2) << "] seconds" << endl;

        Verifier *verifier = new Verifier(setup);
        verifier->prover = prover; // for testing
        cout << "verifier created" << endl;

        // single row lookup check;
        t1 = high_resolution_clock::now();
        RowProof *row_proof = prover->prove_row(0, row_prove_dummy > 0);
        t2 = high_resolution_clock::now();
        cout << "row proof generation complete in [" << get_time(t1, t2) << "] seconds" << endl;
        outfile << "row proof generation complete in [" << get_time(t1, t2) << "] seconds" << endl;
        t1 = high_resolution_clock::now();
        bool ver_res = verifier->verify_row(prover->table_com, 0, row_proof);
        t2 = high_resolution_clock::now();
        cout << "Verification result: 1 " << ver_res << endl;
        cout << "row proof verification complete in [" << get_time(t1, t2) << "] seconds" << endl;
        outfile << "row proof verification complete in [" << get_time(t1, t2) << "] seconds" << endl;
        delete row_proof;

        // passed!

        // multiple rows lookup check

        MultiRowProof *multirowproof;
        for (int round = 0; round < lookup_exp_num; round++)
        {
            row_n = lookup_row_ns[round];
            int *rows = new int[row_n];
            for (int i = 0; i < row_n; i++)
            {
                rows[i] = rand() % max_row;
            }
            t1 = high_resolution_clock::now();
            G1 *sub_row_coms = new G1[row_n];
            multirowproof = prover->prove_rows(rows, row_n, sub_row_coms, rows_prove_dummy);
            t2 = high_resolution_clock::now();
            delete[] sub_row_coms;
            cout << "generate multiple row proof of size " << row_n << " complete in [" << get_time(t1, t2) << "] seconds" << endl;
            outfile << "generate multiple row proof of size " << row_n << " complete in [" << get_time(t1, t2) << "] seconds" << endl;
            t1 = high_resolution_clock::now();
            ver_res = verifier->verify_rows(prover->table_com, multirowproof);
            t2 = high_resolution_clock::now();
            cout << "Verification result multirowproof should be correct " << ver_res << endl;
            cout << "multirow proof verification complete in [" << get_time(t1, t2) << "] seconds" << endl;
            outfile << "multirow proof verification complete in [" << get_time(t1, t2) << "] seconds" << endl;

            delete multirowproof;
            delete[] rows;
        }

        // update row
        cout << "old table com = " << prover->table_com << endl;
        t1 = high_resolution_clock::now();
        data[0][0] = F(rand());
        prover->update_row(0, data[0], max_col, nullptr, prover_table_dummy > 0);
        t2 = high_resolution_clock::now();
        cout << "update row complete in [" << get_time(t1, t2) << "] seconds" << endl;
        cout << "new table com = " << prover->table_com << endl;
        outfile << "update row complete in [" << get_time(t1, t2) << "] seconds" << endl;

        // prove update rows check

        for (int round = 0; round < update_exp_num; round++)
        {
            update_row_n = update_row_ns[round];
            int *update_rows = new int[update_row_n];
            cout << "update rows: " << endl;
            for (int i = 0; i < update_row_n; i++)
            {
                update_rows[i] = i * (max_row / update_row_n) + rand() % (max_row / update_row_n);
                if (i < 10)
                    cout << update_rows[i] << ", ";
            }
            cout << endl;
            F **new_data = new F *[update_row_n];
            for (int i = 0; i < update_row_n; i++)
            {
                new_data[i] = new F[max_col];
                for (int j = 0; j < max_col; j++)
                {
                    new_data[i][j] = F(rand());
                }
            }
            G1 old_table_com = prover->table_com;

            // the old update algorithm
            if (false)
            {
                t1 = high_resolution_clock::now();
                UpdateRowsProof *update_proof_old = prover->update_rows(update_rows, new_data, update_row_n, rows_prove_dummy > 0);
                t2 = high_resolution_clock::now();
                cout << "update proof old generated" << endl;
                cout << "update proof of size " << update_row_n << " old generation complete in [" << get_time(t1, t2) << "] seconds" << endl;
                outfile << "update proof of size " << update_row_n << " old generation complete in [" << get_time(t1, t2) << "] seconds" << endl;

                t1 = high_resolution_clock::now();
                ver_res = verifier->verify_update_rows(old_table_com, prover->table_com, update_proof_old);
                t2 = high_resolution_clock::now();
                cout << "Update Rows Proof verify result (should be correct):  " << ver_res << endl;
                cout << "update proof of size " << update_row_n << " old verification complete in [" << get_time(t1, t2) << "] seconds" << endl;
                outfile << "update proof of size " << update_row_n << " old verification complete in [" << get_time(t1, t2) << "] seconds" << endl;

                delete update_proof_old;
            }

            bool test_update_new = false;
            if (test_update_new)
            {
                // the new update algorithm
                old_table_com = prover->table_com;
                for (int i = 0; i < update_row_n; i++)
                {
                    for (int j = 0; j < max_col; j++)
                    {
                        new_data[i][j] = F(rand());
                    }
                }

                t1 = high_resolution_clock::now();
                cout << "Run update_rows_new" << endl;
                UpdateRowsProof_New *update_proof_new = prover->update_rows_new(update_rows, new_data, update_row_n, rows_prove_dummy > 0);
                t2 = high_resolution_clock::now();
                cout << "update proof of size " << update_row_n << " new generated in [" << get_time(t1, t2) << "] seconds" << endl;
                outfile << "update proof of size " << update_row_n << " new generated in [" << get_time(t1, t2) << "] seconds" << endl;

                t1 = high_resolution_clock::now();
                ver_res = verifier->verify_update_rows_new(old_table_com, prover->table_com, update_proof_new);
                t2 = high_resolution_clock::now();
                cout << "Update Rows Proof New verify result (should be correct):  " << ver_res << endl;
                cout << "update proof of size " << update_row_n << " new verification complete in [" << get_time(t1, t2) << "] seconds" << endl;
                delete update_proof_new;
            }

            bool test_update_newnew = true;
            if (test_update_newnew)
            {
                // the newnew update algorithm: merges two lookup proofs.
                old_table_com = prover->table_com;
                for (int i = 0; i < update_row_n; i++)
                {
                    for (int j = 0; j < max_col; j++)
                    {
                        new_data[i][j] = F(rand());
                    }
                }

                t1 = high_resolution_clock::now();
                cout << "Run update_rows_new" << endl;
                UpdateRowsProof_NewNew *update_proof_newnew = prover->update_rows_newnew(update_rows, new_data, update_row_n, rows_prove_dummy > 0);
                t2 = high_resolution_clock::now();
                cout << "update proof of size " << update_row_n << " newnew generated in [" << get_time(t1, t2) << "] seconds" << endl;
                outfile << "update proof of size " << update_row_n << " newnew generated in [" << get_time(t1, t2) << "] seconds" << endl;

                t1 = high_resolution_clock::now();
                ver_res = verifier->verify_update_rows_newnew(old_table_com, prover->table_com, update_proof_newnew);
                t2 = high_resolution_clock::now();
                cout << "Update Rows Proof NewNew verify result (should be correct):  " << ver_res << endl;
                cout << "update proof of size " << update_row_n << " newnew verification complete in [" << get_time(t1, t2) << "] seconds" << endl;
                outfile << "update proof of size " << update_row_n << " newnew verification complete in [" << get_time(t1, t2) << "] seconds" << endl;
                delete update_proof_newnew;
            }

            delete[] update_rows;
            for (int i = 0; i < update_row_n; i++)
            {
                delete[] new_data[i];
            }
            delete[] new_data;
        }
        delete verifier;
        delete prover;
    }
    else
    {
        Prover_v2 *prover = new Prover_v2(setup);
        cout << "prover created" << endl;
        t1 = high_resolution_clock::now();
        prover->init(data, max_row, max_col, prover_table_dummy > 0);
        t2 = high_resolution_clock::now();
        cout << "prover initialized" << endl;
        cout << "prover init complete in [" << get_time(t1, t2) << "] seconds" << endl;
        outfile << "prover of size (" << max_row << "/" << n_chunks << "x" << max_col << ") initialized in [" << get_time(t1, t2) << "] seconds" << endl;

        Verifier_v2 *verifier = new Verifier_v2(setup, n_chunks);
        verifier->prover = prover; // for debugging
        cout << "verifier created" << endl;

        // single row lookup check;
        t1 = high_resolution_clock::now();
        RowProof_v2 *row_proof = prover->prove_row(0, row_prove_dummy > 0);
        t2 = high_resolution_clock::now();
        cout << "row proof generation complete in [" << get_time(t1, t2) << "] seconds" << endl;
        outfile << "row proof generation complete in [" << get_time(t1, t2) << "] seconds" << endl;
        t1 = high_resolution_clock::now();
        bool ver_res = verifier->verify_row(*prover->chunks_kcom, 0, row_proof);
        t2 = high_resolution_clock::now();
        cout << "Verification result: 1 " << ver_res << endl;
        cout << "row proof verification complete in [" << get_time(t1, t2) << "] seconds" << endl;
        outfile << "row proof verification complete in [" << get_time(t1, t2) << "] seconds" << endl;
        delete row_proof;

        // multiple rows lookup check

        MultiRowProof_v2 *multirowproof;
        for (int round = 0; round < lookup_exp_num; round++)
        {
            row_n = lookup_row_ns[round];
            int *rows = new int[row_n];
            for (int i = 0; i < row_n; i++)
            {
                rows[i] = rand() % max_row;
            }
            t1 = high_resolution_clock::now();
            G1 *sub_row_coms = new G1[row_n];
            multirowproof = prover->prove_rows(rows, row_n, sub_row_coms, rows_prove_dummy);
            t2 = high_resolution_clock::now();
            delete[] sub_row_coms;
            cout << "generate multiple row proof of size " << row_n << " complete in [" << get_time(t1, t2) << "] seconds" << endl;
            outfile << "generate multiple row proof of size " << row_n << " complete in [" << get_time(t1, t2) << "] seconds" << endl;
            t1 = high_resolution_clock::now();
            ver_res = verifier->verify_rows(*prover->chunks_kcom, multirowproof);
            t2 = high_resolution_clock::now();
            cout << "Verification result multirowproof should be correct " << ver_res << endl;
            cout << "multirow proof verification complete in [" << get_time(t1, t2) << "] seconds" << endl;
            outfile << "multirow proof verification complete in [" << get_time(t1, t2) << "] seconds" << endl;

            delete multirowproof;
            delete[] rows;
        }

        // prove update rows check

        for (int round = 0; round < update_exp_num; round++)
        {
            update_row_n = update_row_ns[round];
            int *update_rows = new int[update_row_n];
            cout << "update rows: " << endl;
            for (int i = 0; i < update_row_n; i++)
            {
                update_rows[i] = i * (max_row / update_row_n) + rand() % (max_row / update_row_n);
                if (i < 10)
                    cout << update_rows[i] << ", ";
            }
            cout << endl;
            bool test_new = false;
            if (test_new)
            {
                F **new_data = new F *[update_row_n];
                for (int i = 0; i < update_row_n; i++)
                {
                    new_data[i] = new F[max_col];
                    for (int j = 0; j < max_col; j++)
                    {
                        new_data[i][j] = F(rand());
                    }
                }
                Kopis_com<G1> old_table_com(*prover->chunks_kcom);
                for (int i = 0; i < update_row_n; i++)
                {
                    for (int j = 0; j < max_col; j++)
                    {
                        new_data[i][j] = F(rand());
                    }
                }

                t1 = high_resolution_clock::now();
                cout << "Run update_rows_new" << endl;
                UpdateRowsProof_New_v2 *update_proof_new = prover->update_rows_new(update_rows, new_data, update_row_n, rows_prove_dummy > 0);
                t2 = high_resolution_clock::now();
                cout << "update proof of size " << update_row_n << " new generated in [" << get_time(t1, t2) << "] seconds" << endl;
                outfile << "update proof of size " << update_row_n << " new generated in [" << get_time(t1, t2) << "] seconds" << endl;

                t1 = high_resolution_clock::now();
                ver_res = verifier->verify_update_rows_new(old_table_com, *prover->chunks_kcom, update_proof_new);
                t2 = high_resolution_clock::now();
                cout << "Update Rows Proof New verify result (should be correct):  " << ver_res << endl;
                cout << "update proof of size " << update_row_n << " new verification complete in [" << get_time(t1, t2) << "] seconds" << endl;
                delete update_proof_new;

                for (int i = 0; i < update_row_n; i++)
                {
                    delete[] new_data[i];
                }
                delete[] new_data;
            }

            bool test_newnew = true;
            if (test_newnew)
            {
                F **new_data = new F *[update_row_n];
                for (int i = 0; i < update_row_n; i++)
                {
                    new_data[i] = new F[max_col];
                    for (int j = 0; j < max_col; j++)
                    {
                        new_data[i][j] = F(rand());
                    }
                }
                Kopis_com<G1> old_table_com(*prover->chunks_kcom);
                for (int i = 0; i < update_row_n; i++)
                {
                    for (int j = 0; j < max_col; j++)
                    {
                        new_data[i][j] = F(rand());
                    }
                }

                t1 = high_resolution_clock::now();
                cout << "Run update_rows_new" << endl;
                UpdateRowsProof_NewNew_v2 *update_proof_newnew = prover->update_rows_newnew(update_rows, new_data, update_row_n, rows_prove_dummy > 0);
                t2 = high_resolution_clock::now();
                cout << "update proof of size " << update_row_n << " newnew generated in [" << get_time(t1, t2) << "] seconds" << endl;
                outfile << "update proof of size " << update_row_n << " newnew generated in [" << get_time(t1, t2) << "] seconds" << endl;

                t1 = high_resolution_clock::now();
                ver_res = verifier->verify_update_rows_newnew(old_table_com, *prover->chunks_kcom, update_proof_newnew);
                t2 = high_resolution_clock::now();
                cout << "Update Rows Proof NewNew verify result (should be correct):  " << ver_res << endl;
                cout << "update proof of size " << update_row_n << " newnew verification complete in [" << get_time(t1, t2) << "] seconds" << endl;
                outfile << "update proof of size " << update_row_n << " newnew verification complete in [" << get_time(t1, t2) << "] seconds" << endl;
                delete update_proof_newnew;

                for (int i = 0; i < update_row_n; i++)
                {
                    delete[] new_data[i];
                }
                delete[] new_data;
            }

            delete[] update_rows;
        }
        delete verifier;
        delete prover; // must delete prover before setup: ~Prover requires access to setup.max_col etc.
    }

    outfile.close();
    delete setup;

    for (int i = 0; i < max_row; i++)
    {
        delete[] data[i];
    }
    delete[] data;
}
