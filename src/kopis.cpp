#include "kopis.hpp"

int size_of_Kopis_open(int row_n, int col_dim)
{
    int size = 0; 
    size += sizeof(F) + sizeof(G1*) + sizeof(G1)*col_dim + sizeof(int);
    // now add mipp_proof_k
    size += size_of_mipp_k(row_n); 
    return size;
}

Kopis::Kopis()
{
    this->local_setup = false;
}


// Kopis_G2: 
// use h^{f(t)} to commit to row f. 
// the kopis com is \prod e(g_j, h^{f_j(t)})
// to open at position (r1, r2), first compute h^{\sum beta(r1, j) f_j(t)}, com of f'(y) = \sum beta(r1, j) f_j(y). 
// it is computed as \prod_j [h^{f_j(t)}]^{\beta(r1, j)}. 
// this is computed as the MIPP with known field vector, and the field vector is defined by the betas of r1. 

// it uses KZG_G2. 

Kopis_G2::Kopis_G2()
{
    this->local_setup = false;
}

void Kopis::setup(int max_row, int max_col)
{
    this->local_setup = true;
    this->_max_row = max_row;
    this->_max_col = max_col;
    this->_log_row = int(ceil(log2(max_row)));
    this->_log_col = int(ceil(log2(max_col)));
    gipp = new GIPP();
    kzg = new MultiKZG();
    gipp->setup(_max_row);
    kzg->setup(_log_col);
}

void Kopis_G2::setup(int max_row, int max_col)
{
    this->local_setup = true;
    this->_max_row = max_row;
    this->_max_col = max_col;
    this->_log_row = int(ceil(log2(max_row)));
    this->_log_col = int(ceil(log2(max_col)));
    gipp = new GIPP();
    kzg = new MultiKZG_G2();
    gipp->setup(_max_row);
    kzg->setup(_log_col);
}

void Kopis::setup(GIPP* gipp, MultiKZG* kzg)
{
    this->local_setup = false;
    this->gipp = gipp;
    this->kzg = kzg;
    this->_max_row = gipp->max_size;
    this->_log_row = int(ceil(log2(_max_row)));
    this->_max_col = 1<<kzg->max_dim;
    this->_log_col = kzg->max_dim;
}

void Kopis_G2::setup(GIPP* gipp, MultiKZG_G2* kzg)
{
    this->local_setup = false;
    this->gipp = gipp;
    this->kzg = kzg;
    this->_max_row = gipp->max_size;
    this->_log_row = int(ceil(log2(_max_row)));
    this->_max_col = 1<<kzg->max_dim;
    this->_log_col = kzg->max_dim;
}

Kopis::~Kopis()
{
    if(this->local_setup)
    {
        delete gipp;
        delete kzg;
    }
}

Kopis_G2::~Kopis_G2()
{
    if(this->local_setup)
    {
        delete gipp;
        delete kzg;
    }
}


Kopis_com<G1>* Kopis::commit(F **data, int row_n, int col_dim, int col_n, G1*row_coms)
{
    Kopis_com<G1>* com = new Kopis_com<G1>;
    com->row_coms = new G1[row_n];
    if (row_coms !=nullptr)
    {
        memcpy(com->row_coms, row_coms, row_n*sizeof(G1));
    }
    else
    {
        for (int i = 0; i < row_n; i++)
        {
            com->row_coms[i] = kzg->commit(data[i], col_dim, col_n);
        }
    }
    com->size = row_n;
    
    com->com = ip_G1_G2(com->row_coms, gipp->ck_h2, row_n);
    return com;
    
}

Kopis_com<G2>* Kopis_G2::commit(F **data, int row_n, int col_dim, int col_n, G2*row_coms)
{
    Kopis_com<G2>* com = new Kopis_com<G2>;
    com->row_coms = new G2[row_n];
    if (row_coms !=nullptr)
    {
        memcpy(com->row_coms, row_coms, row_n*sizeof(G2));
    }
    else
    {
        for (int i = 0; i < row_n; i++)
        {
            com->row_coms[i] = kzg->commit(data[i], col_dim, col_n);
        }
    }
    com->size = row_n;
    com->com = ip_G1_G2(gipp->ck_g1, com->row_coms, row_n);
    return com;
}


Kopis_com<G2>* Kopis_G2::commit(F *data, int row_n, G2*row_coms)
{
    Kopis_com<G2>* com = new Kopis_com<G2>;
    com->row_coms = new G2[row_n];
    if (row_coms !=nullptr)
    {
        memcpy(com->row_coms, row_coms, row_n*sizeof(G2));
    }
    else
    {
        for (int i = 0; i < row_n; i++)
        {
            com->row_coms[i] = kzg->h*data[i];
        }
    }
    com->size = row_n;
    com->com = ip_G1_G2(gipp->ck_g1, com->row_coms, row_n);
    return com;
}

void Kopis::Kopisopen(Kopis_open *open_res, F **data, F *point_row, F*point_col, int row_n, int col_dim, int col_n, G1*row_coms)
{
    if (col_dim < 0) col_n = 1<< col_dim;
    open_res->col_dim = col_dim;
    bool row_coms_given = row_coms!=nullptr;
    if (!row_coms_given)
    {
        cout << "Warning: row_coms is not provided. It is time comsuming to compute row_coms again in open " <<endl;
        row_coms = new G1[row_n];
        for (int i = 0; i < row_n; i++)
        {
            row_coms[i] = kzg->commit(data[i], col_dim, col_n);
        }
    }

    int log_row = int(ceil(log2(row_n)));
    int log_col = col_dim;

    // when row_n>=4, uses an ipa proof. 
    if (row_n>=4)
    {
        open_res->ipa_proof = gipp->generate_proof_k(row_coms, point_row, F_ONE, row_n, true);
    }
    else
    {
        open_res->ipa_proof = nullptr;
        G1 r1_com = row_coms[0] * beta(point_row, 0, log_row);
        for (int i = 1; i<row_n; i++)
        {
            r1_com += row_coms[i] * beta(point_row, i, log_row);
        }
    }

    open_res->kzg_proof = new G1[log_col];
    open_res->val = F_ZERO; 
    // construct \sum_x beta(r1,x) f_x(y) polynomial
    F* beta_p1 = new F[row_n]; 
    beta_fullvec(beta_p1, point_row, log_row);
    F* beta_poly = new F[col_n]; 
    for (int i = 0; i<col_n; i++)
    {
        beta_poly[i] = 0;
        for (int j = 0; j<row_n; j++)
        {
            beta_poly[i] += beta_p1[j]*data[j][i];
        }
    }
    G1* tmp[log_col];
    F* r2 = point_col; // r1 is point[0:log_row-1]. 
    F beta_r1 = beta(point_row, 0, log_row); 
    kzg->prove(open_res->kzg_proof, beta_poly, r2, col_dim, col_n);
    open_res->val = kzg->eval(beta_poly, r2, col_dim, col_n);
    if (!row_coms_given)
    {
        delete[] row_coms;
    }
    delete[] beta_p1;
    delete[] beta_poly; 
}

void Kopis_G2::Kopisopen(Kopis_open_G2 *open_res, F **data, F *point_row, F*point_col, int row_n, int col_dim, int col_n, G2*row_coms)
{
    if (col_n < 0) col_n = 1<<col_dim;
    open_res->col_dim = col_dim;
    bool row_coms_given = row_coms!=nullptr;
    if (!row_coms_given)
    {
        cout << "Warning: row_coms is not provided. It is time comsuming to compute row_coms again in open " <<endl;
        row_coms = new G2[row_n];
        for (int i = 0; i < row_n; i++)
        {
            row_coms[i] = kzg->commit(data[i], col_n);
        }
    }

    int log_row = int(ceil(log2(row_n)));
    int log_col = col_dim;

    // when row_n>=4, uses an ipa proof. 
    if (row_n>=4)
    {
        open_res->ipa_proof = gipp->generate_proof_k_G2(row_coms, point_row, F_ONE, row_n, true);
    }
    else
    {
        open_res->ipa_proof = nullptr;
        G2 r1_com = row_coms[0] * beta(point_row, 0, log_row);
        for (int i = 1; i<row_n; i++)
        {
            r1_com += row_coms[i] * beta(point_row, i, log_row);
        }
    }

    open_res->kzg_proof = new G2[log_col];
    open_res->val = F_ZERO; 
    // construct \sum_x beta(r1,x) f_x(y) polynomial
    F* beta_p1 = new F[row_n]; 
    beta_fullvec(beta_p1, point_row, log_row);
    F* beta_poly = new F[col_n]; 
    for (int i = 0; i<col_n; i++)
    {
        beta_poly[i] = 0;
        for (int j = 0; j<row_n; j++)
        {
            beta_poly[i] += beta_p1[j]*data[j][i];
        }
    }
    G2* tmp[log_col];
    F* r2 = point_col; // r1 is point[0:log_row-1]. 
    F beta_r1 = beta(point_row, 0, log_row); 
    kzg
    ->prove(open_res->kzg_proof, beta_poly, r2, col_dim, col_n);
    open_res->val = kzg->eval(beta_poly, r2, col_dim, col_n);
    if (!row_coms_given)
    {
        delete[] row_coms;
    }
    delete[] beta_p1;
    delete[] beta_poly;
}

void Kopis::Kopisopen(Kopis_open*open_res, F **data, F *point_row, F*point_col, Kopis_com<G1>*k_com, int col_dim, int col_n)
{
    int row_n = k_com->size;
    G1* row_coms = k_com->row_coms;
    Kopisopen(open_res, data, point_row, point_col, row_n, col_dim, col_n, row_coms);
}

void Kopis_G2::Kopisopen(Kopis_open_G2*open_res, F **data, F *point_row, F*point_col, Kopis_com<G2>*k_com, int col_dim, int col_n)
{
    int row_n = k_com->size;
    G2* row_coms = k_com->row_coms;
    Kopisopen(open_res, data, point_row, point_col, row_n, col_dim, col_n, row_coms);
}

Kopis_open* Kopis::Kopisopen(F **data, F *point_row, F*point_col, int row_n, int col_dim, int col_n, G1* row_coms)
{
    Kopis_open* open_res = new Kopis_open;
    Kopisopen(open_res, data, point_row, point_col, row_n, col_dim, col_n, row_coms);
    return open_res;
}

Kopis_open_G2* Kopis_G2::Kopisopen(F **data, F *point_row, F*point_col, int row_n, int col_dim, int col_n, G2* row_coms)
{
    Kopis_open_G2* open_res = new Kopis_open_G2;
    Kopisopen(open_res, data, point_row, point_col, row_n, col_dim, col_n, row_coms);
    return open_res;
}   

Kopis_open*Kopis::Kopisopen(F **data, F *point_row, F*point_col, Kopis_com<G1>*k_com, int col_dim, int col_n)
{
    Kopis_open* open_res = new Kopis_open;
    Kopisopen(open_res, data, point_row, point_col, k_com->size, col_dim, col_n, k_com->row_coms);
    return open_res;
}

Kopis_open_G2*Kopis_G2::Kopisopen(F **data, F *point_row, F*point_col, Kopis_com<G2>*k_com, int col_dim, int col_n)
{
    Kopis_open_G2* open_res = new Kopis_open_G2;
    Kopisopen(open_res, data, point_row, point_col, k_com->size, col_dim, col_n, k_com->row_coms);
    return open_res;
}

// for single column special case. 
Kopis_open_G2*Kopis_G2::Kopisopen(F *data, F *point, Kopis_com<G2>*k_com)
{
    Kopis_open_G2* open_res = new Kopis_open_G2;
    G2*row_coms = k_com->row_coms;
    int row_n = k_com->size;
    bool row_coms_given = row_coms!=nullptr;
    if (!row_coms_given)
    {
        cout << "Warning: row_coms is not provided. It is time comsuming to compute row_coms again in open " <<endl;
        row_coms = new G2[row_n];
        for (int i = 0; i < row_n; i++)
        {
            row_coms[i] = kzg->h*data[i];
        }
    }

    int log_row = int(ceil(log2(row_n)));
    int log_col = 0;

    // when row_n>=4, uses an ipa proof. 
    if (row_n>=4)
    {
        open_res->ipa_proof = gipp->generate_proof_k_G2(row_coms, point, F_ONE, row_n, true);
    }
    else
    {
        open_res->ipa_proof = nullptr;
        G2 r1_com = row_coms[0] * beta(point, 0, log_row);
        for (int i = 1; i<row_n; i++)
        {
            r1_com += row_coms[i] * beta(point, i, log_row);
        }
    }

    open_res->kzg_proof = new G2[0];
    open_res->val = F_ZERO;
    for (int i = 0; i<row_n; i++)
    {
        open_res->val += data[i]*beta(point, i, log_row);
    }
    if (!row_coms_given)
    {
        delete[] row_coms;
    }
    return open_res;
}

bool Kopis::verify(const Kopis_com<G1>& com, F *point_row, F*point_col, Kopis_open *open_res)
{
    bool ver_res = true;
    // first check gipa if required
    G1 f_r1_com; 
    int log_row = int(ceil(log2(com.size)));
    if (open_res->ipa_proof!=nullptr)
    {
        if (!gipp->verify_proof_k(open_res->ipa_proof, com.com, point_row, F_ONE, true))
        {
            cout << "Kopis verify: gipa proof check fail" << endl;
            ver_res = false;
        }   
        f_r1_com = open_res->ipa_proof->z;
    }
    else
    {
        // compute again. 
        f_r1_com = com.row_coms[0] * beta(point_row, 0, log_row);
        for (int i = 1; i<com.size; i++)
        {
            f_r1_com += com.row_coms[i] * beta(point_row, i, log_row);
        }

    }    
    // now kzg check
    if (!kzg->verify(f_r1_com, point_col, open_res->val, open_res->kzg_proof, open_res->col_dim))
    {
        cout << "Kopis verify: kzg proof check fail" << endl;
        ver_res = false;
    }
    return ver_res;
}

bool Kopis_G2::verify(const Kopis_com<G2>&com, F *point_row, F*point_col, Kopis_open_G2*open_res)
{
    bool ver_res = true;
    // first check gipa if required
    G2 f_r1_com; 
    int log_row = int(ceil(log2(com.size)));
    if (open_res->ipa_proof!=nullptr)
    {
        if (!gipp->verify_proof_k_G2(open_res->ipa_proof, com.com, point_row, F_ONE, true))
        {
            cout << "Kopis verify: gipa proof check fail" << endl;
            ver_res = false;
        }   
        f_r1_com = open_res->ipa_proof->z;
    }
    else
    {
        // compute again. 
        f_r1_com = com.row_coms[0] * beta(point_row, 0, log_row);
        for (int i = 1; i<com.size; i++)
        {
            f_r1_com += com.row_coms[i] * beta(point_row, i, log_row);
        }

    }    
    // now kzg check
    if (!kzg->verify(f_r1_com, point_col, open_res->val, open_res->kzg_proof, open_res->col_dim))
    {
        cout << "Kopis verify: kzg proof check fail" << endl;
        ver_res = false;
    }
    return ver_res;
}

