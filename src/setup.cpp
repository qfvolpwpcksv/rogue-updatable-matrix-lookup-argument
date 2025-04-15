#include "setup.hpp"

Setup::Setup(int max_row, int max_col, int max_chunks, bool dummy)
{
    _max_row = max_row;
    _max_col = max_col;
    _max_chunks = max_chunks;
    _log_row = int(ceil(log2(max_row)));
    _log_col = int(ceil(log2(max_col)));
    _log_max_chunks = int(ceil(log2(max_chunks)));

    hashAndMapToG1(g1, "random-g1");
    hashAndMapToG2(h2, "random-h2");
    fr = F(rand());
    gtr = my_loop(g1, h2);

    G1_zero = g1 * 0;
    G2_zero = h2 * 0;
    GT_one = my_loop(g1, h2);
    GT_zero = my_loop(G1_zero, G2_zero);


    tvec = new F[_log_row + _log_col];
    h2tvec = new G2[_log_row + _log_col];
    g1tvec = new G1[_log_row + _log_col];

    beta_t_part1 = new F[_max_row];
    beta_t_all = new F[_max_row * _max_col];

    for (int i = 0; i < _log_row + _log_col; i++)
        tvec[i] = F(rand());

    if (dummy)
    {
        for (int i = 0; i < _log_row + _log_col; i++)
        {
            h2tvec[i] = h2;
            g1tvec[i] = g1;
        }
    }
    else
    {
        Fvec_G2scalar(h2tvec, tvec, h2, _log_row + _log_col);
        Fvec_G1scalar(g1tvec, tvec, g1, _log_row + _log_col);
        beta_fullvec(beta_t_part1, tvec, _log_row);
        beta_fullvec(beta_t_all, tvec, _log_row + _log_col);
    }

    // tvec_towers
    h2tvec_tower_part1 = new G2 *[_log_row + 1];
    g1tvec_tower_part1 = new G1 *[_log_row + 1];
    g1tvec_tower_all = new G1 *[_log_row + _log_col + 1];
    g1tvec_tower_part2 = g1tvec_tower_all + _log_row;
    if (dummy)
    {
        for (int i = 0; i < _log_row + 1; i++)
        {
            h2tvec_tower_part1[i] = new G2[1 << (_log_row - i)];
            g1tvec_tower_part1[i] = new G1[1 << (_log_row - i)];
            for (int j = 0; j < 1 << (_log_row - i); j++)
            {
                h2tvec_tower_part1[i][j] = h2;
                g1tvec_tower_part1[i][j] = g1;
            }
        }
        for (int i = 0; i < _log_row + _log_col + 1; i++)
        {
            g1tvec_tower_all[i] = new G1[1 << (_log_row + _log_col - i)];
            for (int j = 0; j < 1 << (_log_row + _log_col - i); j++)
            {
                g1tvec_tower_all[i][j] = g1;
            }
        }
    }
    else
    {
        compute_tvec_tower(h2tvec_tower_part1, h2, beta_t_part1, _log_row);
        compute_tvec_tower(g1tvec_tower_part1, g1, beta_t_part1, _log_row);
        compute_tvec_tower(g1tvec_tower_all, g1, beta_t_all, _log_row + _log_col);
    }
    delete[] beta_t_part1;
    delete[] beta_t_all;

    logcol_kzg = new MultiKZG();
    logcol_kzg->setup(_log_col, g1, h2, tvec + _log_row, g1tvec_tower_part2, h2tvec + _log_row);

    logrow_kzg_G2 = new MultiKZG_G2();
    logrow_kzg_G2->setup(_log_row, h2, g1, tvec, h2tvec_tower_part1, g1tvec);

    logrowcol_kzg = new MultiKZG();
    logrowcol_kzg->setup(_log_row + _log_col, g1, h2, tvec, g1tvec_tower_all, h2tvec);

    gipp = new GIPP();

    int _max_of_log_rows_and_log_chunks = _log_max_chunks;
    if (_log_row > _log_max_chunks)
        _max_of_log_rows_and_log_chunks = _log_row;
    int _max_of_rows_and_chunks = 1 << _max_of_log_rows_and_log_chunks;
    cout << "_max_of_rows_and_chunks = " << _max_of_rows_and_chunks << endl;

    gipp->setup(_max_row*_max_chunks, &g1, &h2, dummy);
    

    kopis = new Kopis();
    kopis->setup(gipp, logcol_kzg);

    if (max_chunks > 1)
    {
        kopis_chunks = new Kopis();
        kopis_chunks->setup(gipp, logrowcol_kzg);
    }

    kopis_g2 = new Kopis_G2();
    kopis_g2->setup(gipp, logrow_kzg_G2);

    precom_logk_gj = new G1[_log_max_chunks + _log_row + 1];
    for (int k = 0; k <= _log_max_chunks + _log_row; k++)
    {
        if (dummy)
        {
            precom_logk_gj[k] = g1;
        }
        else 
        {
            if (k == 0)
                precom_logk_gj[k] = gipp->ck_g1[0];
            else
            {
                precom_logk_gj[k] = precom_logk_gj[k-1];
                for (int j = (1<<(k-1)); j < (1 << k); j++)
                {
                    precom_logk_gj[k] += gipp->ck_g1[j];
                }
            }
        }
    }

    precom_logk_l_gj_htl = new GT *[_log_max_chunks + _log_row + 1];
    for (int i = 0; i <= _log_max_chunks + _log_row; i++)
    {
        precom_logk_l_gj_htl[i] = new GT[_log_row];
        for (int l = 0; l < _log_row; l++)
        { // ck_g1
            if (dummy)
            {
                precom_logk_l_gj_htl[i][l] = gtr;
            }
            else
                precom_logk_l_gj_htl[i][l] = my_loop(precom_logk_gj[i], h2tvec[l]);
        }
    }
}

Setup::~Setup()
{

    delete[] tvec;
    delete[] h2tvec;
    delete[] g1tvec;

    for (int l = 0; l < _log_row + 1; l++)
        delete[] h2tvec_tower_part1[l];
    delete[] h2tvec_tower_part1;
    for (int l = 0; l < _log_row + 1; l++)
        delete[] g1tvec_tower_part1[l];
    delete[] g1tvec_tower_part1;
    for (int l = 0; l < _log_row + _log_col + 1; l++)
        delete[] g1tvec_tower_all[l];
    delete[] g1tvec_tower_all;

    delete logcol_kzg;
    delete logrow_kzg_G2;
    delete logrowcol_kzg;
    delete gipp;
    delete kopis;
    delete kopis_g2;
    if (_max_chunks > 1)
    {
        delete kopis_chunks;
    }

    delete[] precom_logk_gj;
    for (int i = 0; i < _log_row + 1; i++)
        delete[] precom_logk_l_gj_htl[i];
    delete[] precom_logk_l_gj_htl;
}

//  O(data_size*log_row)  $O(log_row) mulvec of size data_size.
void multi_hyper_of_f_as_rowi(G1 *res, F *data, int row_i, int log_row, int dim, G1 **tvec_tower_all, G1 *data_com_p, int data_size)
{

    if (data_size < 0)
        data_size = 1 << dim;
    G1 data_com;
    if (data_com_p != nullptr)
        data_com = *data_com_p;
    else
        data_com = ip_F_G1(data, tvec_tower_all[log_row], data_size);
    F *i_points = new F[log_row];
    int_to_Fvec(i_points, row_i, log_row);
    for (int l = 0; l < log_row; l++)
    {
        if (l < log_row - 1)
            res[l] = ip_F_G1(data, tvec_tower_all[l + 1] + ((row_i & ((1 << (log_row - l - 1)) - 1)) << dim), data_size);
        else
            res[l] = data_com;
        res[l] *= (2 * i_points[l] - F_ONE);
    }
    delete[] i_points;
}

G1 multi_beta_rowi_f_T(F *data, G1 *g1beta_t, int row_i, int dim, int data_size)
{
    return ip_F_G1(data, g1beta_t + (row_i << dim), data_size);
}

// the beta function beta(x,i). open at point.
// the resulting quotient polynomials are all monomials (in lagrange/beta basis)
// beta(x, i) - beta(p, i) = (2*i[0]-1) * (x0 - p0) * beta(x[1:], i[1:]) + ...
// res is the coefficients. dim many
// the corresponding monomial is not specified. it is defined by beta_i[j+1].
void compute_beta_q_coef(F *res, F *beta_i, F *point, int dim)
{
    F tmp = F_ONE;
    for (int j = 0; j < dim; j++)
    {
        // res[j] = tmp * (2*beta_i[j]-F_ONE);
        // tmp *= point[j] * (2*beta_i[j]-F_ONE) + (F_ONE-beta_i[j]);
        if (beta_i[j] == F_ZERO)
        {
            res[j] = -tmp;
            tmp *= (F_ONE - point[j]);
        }
        else
        {
            res[j] = tmp;
            tmp *= point[j];
        }
    }
}

// log_row G1mulvec of size col + col (kzg open: only logcol G1mulvec. ).
void multi_Q_of_beta_rowi_f(G1 *res, F *data, F *point, int row_i, int log_row, int dim, G1 **tvec_tower_all, const G1 &g1, int data_size)
{
    F *beta_q_coef = new F[log_row];
    F *i_binvec = new F[log_row];
    int_to_Fvec(i_binvec, row_i, log_row);
    compute_beta_q_coef(beta_q_coef, i_binvec, point, log_row);
    F *fi_q_coef = new F[1 << dim];
    multi_Q_coef_of_f(fi_q_coef, data, point + log_row, dim, tvec_tower_all + log_row, g1, F_ONE, data_size);

    int shift;
    for (int j = 0; j < log_row; j++)
    {
        shift = row_i & ((1 << (log_row - j - 1)) - 1);
        res[j] = ip_F_G1(data, tvec_tower_all[j + 1] + (shift << dim), 1 << (dim)) * beta_q_coef[j];
    }
    F beta_p1_i = beta(point, row_i, log_row);
    for (int j = 0; j < dim; j++)
    {
        shift = 1 << (dim - 1 - j);
        res[log_row + j] = ip_F_G1(fi_q_coef + shift, tvec_tower_all[log_row + j + 1], shift) * beta_p1_i;
    }


    delete[] beta_q_coef;
    delete[] i_binvec;
    delete[] fi_q_coef;
}
