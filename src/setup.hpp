#pragma once

#include "config_pc.hpp"
#include "basic_utils.hpp"
#include "gipa.hpp"
#include "multi_kzg.hpp"
#include "kopis.hpp"
#include <type_traits>

class Setup
{
public:
    Setup(int max_row, int max_col, int max_chunks, bool dummy = false);
    ~Setup();

    int _max_row; // actual table size will be max_row*n_chunks
    int _max_col;
    int _log_row;
    int _log_col;
    int _max_chunks;
    int _log_max_chunks;

    MultiKZG *logcol_kzg; // to represent a single row of length max_col, a polynomial of log_col variables.
    MultiKZG_G2 *logrow_kzg_G2;
    MultiKZG *logrowcol_kzg; // larger kzg
    GIPP* gipp; // use a large gipp for the entire table rows (chunk_size * max_chunks)
    Kopis *kopis;
    
    Kopis *kopis_chunks;
    Kopis_G2 *kopis_g2;

    G1 g1;
    G2 h2;

    // precomputation for lookup argument.
    // precomputation: prod_j e(g_j, h^{t_l}).
    GT **precom_logk_l_gj_htl; // the first index is for the (log) size of vectors, the second is fixed by the size of tvec.
    G1 *precom_logk_gj; // prod_j g_j

    // for kzg
    G1 **g1tvec_tower_part1; // g1tvec_tower_part1[l][i] = g1*beta(t[l:_log_row], i[l:_log_row]) // for efficiency, cut i.

    G1 **g1tvec_tower_part2; // g1tvec_tower_part2[l][i] = g1*beta(t[_log_row+l:_log_row+_log_col], i[_log_row+l:_log_row+_log_col]) // for efficiency, cut i.

    G1 **g1tvec_tower_all; // g1tvec_tower_all[l][i] = g1*beta(t[l:_log_row+_log_col], i[l:_log_row+_log_col]) // for efficiency, cut i.

    G2 *h2tvec; // the size is _log_row+_log_col
    G2 **h2tvec_tower_part1; // replace the above. used in update_rows (old). Kopis_G2/KZG_G2.
    G1 *g1tvec;              // used in KZG_G2

    // these three should be private.
    F _alpha; // for MIPP/TIPP
    F _beta;  // for MIPP/TIPP
    // vector<F> tvec;
    F *tvec;

    G1 G1_zero;
    G2 G2_zero;
    GT GT_one, GT_zero;

    F fr;
    GT gtr; 

private:
    F *beta_t_all;   // beta_t_all[i] = beta(t, i) dim log_row+log_col
    F *beta_t_part1; // over log_row.
};

void multi_hyper_of_f_as_rowi(G1 *res, F *data, int row_i, int log_row, int dim, G1 **tvec_tower_all, G1 *data_com_p = nullptr, int data_size = -1); // hyperproof contribution of the polynomial as in row_i
G1 multi_beta_rowi_f_T(F *data, G1 *g1beta_t, int row_i, int dim, int data_size);                                                                    // note that g1beta_t is total
void multi_Q_of_beta_rowi_f(G1 *res, F *data, F *point, int row_i, int log_row, int dim, G1 **tvec_tower_all, const G1 &g1, int data_size = -1);
