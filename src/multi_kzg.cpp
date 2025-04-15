#include "multi_kzg.hpp"

// complexity is O(2^dim) = O(data_size) 
F multi_eval(F *data, F *point, int dim, int data_size)
{
    if (data_size < 0)
        data_size = 1 << dim;
    F res;
    F *betas = new F[1 << dim];
    beta_fullvec(betas, point, dim);
    res = ip_F_F(data, betas, data_size);
    
    delete[] betas;
    return res;
}






// multilinear kzg verify:
// e(f_com/g^f(point), h) = \prod e(q, h^{t_i - point_i})
// r is the point
// f_com is

bool MultiKZGVerify(const G1 &f_com, F *point, F val, G1 *proof, G2 *ht, int dim, const G1 &g, const G2 &h)
{
    GT lhs, rhs;
    millerLoop(lhs, f_com - g * val, h);
    // rhs is GIP of q and (ht - h^r)
    G2 *hr = new G2[dim];
    Fvec_G2scalar(hr, point, h, dim);
    G2* ht_minus_hr = new G2[dim];
    G2vec_sub(ht_minus_hr, ht, hr, dim);
    rhs = ip_G1_G2(proof, ht_minus_hr, dim);
    delete[] hr;
    delete[] ht_minus_hr;
    return pre_exp_GT_equal_check(lhs, rhs);
}

bool MultiKZGVerify(const G2&f_com, F*point, F val, G2*proof, G1*gt, int dim, const G2&h, const G1&g)
{
    GT lhs, rhs;
    millerLoop(lhs, g, f_com - h * val);
    G1 *gr = new G1[dim];
    Fvec_G1scalar(gr, point, g, dim);
    G1* gt_minus_hr = new G1[dim];
    G1vec_sub(gt_minus_hr, gt, gr, dim);
    rhs = ip_G1_G2(gt_minus_hr, proof, dim);
    delete[] gr;
    delete[] gt_minus_hr;
    return pre_exp_GT_equal_check(lhs, rhs);
}

// MultiKZG class

MultiKZG::MultiKZG()
{
    local_setup = false;
}

MultiKZG_G2::MultiKZG_G2()
{
    local_setup = false;
}

void MultiKZG::setup(int max_dim)
{
    local_setup = true;
    this->max_dim = max_dim;
    hashAndMapToG1(g, "random-g");
    hashAndMapToG2(h, "random-h");

    tvec = new F[max_dim];
    for (int i = 0; i < max_dim; i++)
    {
        tvec[i] = F(rand());
    }

    htvec = new G2[max_dim];
    for (int i = 0; i < max_dim; i++)
    {
        htvec[i] = h * tvec[i];
    }

    F* beta_t = new F[1<<max_dim];
    beta_fullvec(beta_t, tvec, max_dim);
    tvec_tower = new G1*[max_dim+1];
    compute_tvec_tower(tvec_tower, g, beta_t, max_dim);
    delete[] beta_t;
}

void MultiKZG_G2::setup(int max_dim)
{
    local_setup = true;
    this->max_dim = max_dim;
    hashAndMapToG1(g, "random-g");
    hashAndMapToG2(h, "random-h");

    tvec = new F[max_dim];
    for (int i = 0; i < max_dim; i++)
    {
        tvec[i] = F(rand());
    }

    gtvec = new G1[max_dim];
    for (int i = 0; i < max_dim; i++)
    {
        gtvec[i] = g * tvec[i];
    }

    F* beta_t = new F[1<<max_dim];
    beta_fullvec(beta_t, tvec, max_dim);
    tvec_tower = new G2*[max_dim+1];
    compute_tvec_tower<G2>(tvec_tower, h, beta_t, max_dim);
    delete[] beta_t;
}

void MultiKZG::setup(int max_dim, const G1 &g, const G2 &h, F *tvec, G1 **tvec_tower, G2 *htvec)
{
    local_setup = false;
    this->max_dim = max_dim;
    this->g = g;
    this->h = h;
    this->tvec = tvec;
    this->tvec_tower = tvec_tower;
    this->htvec = htvec;
}

void MultiKZG_G2::setup(int max_dim, const G2 &h, const G1 &g, F *tvec, G2 **tvec_tower, G1 *gtvec)
{
    local_setup = false;
    this->max_dim = max_dim;
    this->g = g;
    this->h = h;
    this->tvec = tvec;
    this->tvec_tower = tvec_tower;
    this->gtvec = gtvec;
}

MultiKZG::~MultiKZG()
{
    if (local_setup)
    {
        delete[] tvec;
        delete[] htvec;
        for (int i = 0; i < max_dim+1; i++)
        {
            delete[] tvec_tower[i];
        }
        delete[] tvec_tower;
    }
}

MultiKZG_G2::~MultiKZG_G2()
{
    if (local_setup)
    {
        delete[] tvec;
        delete[] gtvec;
        for (int i = 0; i < max_dim+1; i++)
        {
            delete[] tvec_tower[i];
        }
        delete[] tvec_tower;
    }
}

G1 MultiKZG::commit(F *data, int data_dim, int data_size)
{
    if (data_size < 0) data_size = 1<< data_dim;
    return multi_eval_T<G1>(data, tvec_tower[max_dim-data_dim], data_size);
}

void MultiKZG::commit(G1&com, F *data, int data_dim, int data_size)
{
    if (data_size < 0) data_size = 1<< data_dim;
    multi_eval_T<G1>(com, data, tvec_tower[max_dim-data_dim], data_size);
}

G2 MultiKZG_G2::commit(F *data, int data_dim, int data_size)
{
    if (data_size < 0) data_size = 1<< data_dim;
    return multi_eval_T<G2>(data, tvec_tower[max_dim-data_dim], data_size);
}

void MultiKZG_G2::commit(G2&com, F *data, int data_dim, int data_size)
{
    if (data_size < 0) data_size = 1<< data_dim;
    multi_eval_T<G2>(com, data, tvec_tower[max_dim-data_dim], data_size);
}

G1 *MultiKZG::prove(F *data, F *point, int data_dim, int data_size, F external_multiplier)
{
    G1 *qs = new G1[data_dim];
    prove(qs, data, point, data_dim, data_size, external_multiplier);
    return qs;
}

void MultiKZG::prove(G1 *proof, F *data, F *point, int data_dim, int data_size, F external_multiplier)
{
    multi_Q_of_f(proof, data, point, data_dim, tvec_tower+(max_dim-data_dim), g, external_multiplier, data_size);
}

G2 *MultiKZG_G2::prove(F *data, F *point, int data_dim, int data_size, F external_multiplier)
{
    G2 *qs = new G2[data_dim];
    prove(qs, data, point, data_dim, data_size, external_multiplier);
    return qs;
}

void MultiKZG_G2::prove(G2 *proof, F *data, F *point, int data_dim, int data_size, F external_multiplier)
{
    multi_Q_of_f(proof, data, point, data_dim, tvec_tower + (max_dim - data_dim), h, external_multiplier, data_size);
}

F MultiKZG::eval(F *data, F *point, int data_dim, int data_size)
{
    return multi_eval(data, point, data_dim, data_size);
}

F MultiKZG_G2::eval(F *data, F *point, int data_dim, int data_size)
{
    return multi_eval(data, point, data_dim, data_size);
}

void MultiKZG::KZGopen(MultiKZGOpen<G1> *open_res, F *data, F *point, int data_dim, int data_size)
{
    open_res->dim = data_dim;
    open_res->result = eval(data, point, data_dim, data_size);
    open_res->proof = prove(data, point, data_dim,  data_size);
}

void MultiKZG_G2::KZGopen(MultiKZGOpen<G2> *open_res, F *data, F *point, int data_dim, int data_size)
{
    open_res->dim = data_dim;   
    open_res->result = eval(data, point, data_dim, data_size);
    open_res->proof = prove(data, point, data_dim, data_size);
}

// require the current kzg to be setup for dim log_row+log_col
void MultiKZG::KZGopen_matrix(MultiKZGOpen<G1> *open_res, F**data, F*point_row, F*point_col, int row_dim, int col_dim, int row_size, int col_size)
{ 
    if (row_size <0) row_size = 1<< row_dim;
    if (col_size <0) col_size = 1<< col_dim;
    F*flat_data = new F[row_size<<col_dim];
    for (int i = 0; i < row_size; i++)
    {
        memcpy(flat_data+i*col_size, data[i], col_size*sizeof(F));
        for (int j  = col_size; j< (1<<col_dim); j++)
        {
            flat_data[i*col_size+j] = F_ZERO;
        }
    }
    F*flat_point = new F[row_dim+col_dim];
    memcpy(flat_point, point_row, row_dim*sizeof(F));
    memcpy(flat_point+row_dim, point_col, col_dim*sizeof(F));
    KZGopen(open_res, flat_data, flat_point, row_dim+col_dim, row_size<<col_dim);
    delete[] flat_data;
    delete[] flat_point;
}

// require the current kzg to be setup for dim log_row+log_col
void MultiKZG_G2::KZGopen_matrix(MultiKZGOpen<G2> *open_res, F**data, F*point_row, F*point_col, int row_dim, int col_dim, int row_size, int col_size)
{
    if (row_size <0) row_size = 1<< row_dim;
    if (col_size <0) col_size = 1<< col_dim;
    F*flat_data = new F[row_size<<col_dim];
    for (int i = 0; i < row_size; i++)
    {
        memcpy(flat_data+i*col_size, data[i], col_size*sizeof(F));
        for (int j  = col_size; j< (1<<col_dim); j++)
        {
            flat_data[i*col_size+j] = F_ZERO;
        }
    }
    F*flat_point = new F[row_dim+col_dim];
    memcpy(flat_point, point_row, row_dim*sizeof(F));
    memcpy(flat_point+row_dim, point_col, col_dim*sizeof(F));
    KZGopen(open_res, flat_data, flat_point, row_dim+col_dim, row_size<<col_dim);
    delete[] flat_data;
    delete[] flat_point;
}

MultiKZGOpen<G1> *MultiKZG::KZGopen(F *data, F *point, int data_dim, int data_size)
{
    MultiKZGOpen<G1> *open_res = new MultiKZGOpen<G1>;
    KZGopen(open_res, data, point, data_dim, data_size);
    return open_res;
}

MultiKZGOpen<G2> *MultiKZG_G2::KZGopen(F *data, F *point, int data_dim, int data_size)
{
    MultiKZGOpen<G2> *open_res = new MultiKZGOpen<G2>;
    KZGopen(open_res, data, point, data_dim, data_size);
    return open_res;
}

bool MultiKZG::verify(const G1 &f_com, F *point, MultiKZGOpen<G1> *open)
{
    return MultiKZGVerify(f_com, point, open->result, open->proof, htvec + (max_dim - open->dim), open->dim, g, h);
}

bool MultiKZG::verify(const G1 &f_com, F *point, F val, G1 *proof, int dim)
{
    return MultiKZGVerify(f_com, point, val, proof, htvec+(max_dim-dim), dim, g, h);
}

bool MultiKZG_G2::verify(const G2 &f_com, F *point, MultiKZGOpen<G2> *open)
{
    return MultiKZGVerify(f_com, point, open->result, open->proof, gtvec + (max_dim-open->dim), open->dim, h, g);
}

bool MultiKZG_G2::verify(const G2 &f_com, F *point, F val, G2 *proof, int dim)
{
    return MultiKZGVerify(f_com, point, val, proof, gtvec + (max_dim-dim), dim, h, g);
}
