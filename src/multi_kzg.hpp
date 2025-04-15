#pragma once
#include "basic_utils.hpp"

template<class T>
struct MultiKZGOpen{
    F result;
    T* proof;
    int dim; 
    ~MultiKZGOpen(){
        delete proof;
    }
};

F multi_eval(F*data, F*point, int dim, int data_size=-1); // need dim for point size

template <class T>
T multi_eval_T(F*data, T*gbeta_t, int data_size)
{
    T res;
    mulVec<T>(res, gbeta_t, data,  data_size);
    return res;
}


template <class T>
void multi_eval_T(T&res, F*data, T*gbeta_t, int data_size)
{
    mulVec<T>(res, gbeta_t, data, data_size);
}

// new complexity is O(data_size). especially, it uses only O(log(col)) G1mulvec. 
// the polynomial is represented by data array = lagrange coefficients.
// (1-x0)R_part1 = -(x0-p0)R + (1-p0) R 
// x0 R_part2 = (x0-p0)R + p0 R
// the quotient is -R_part1 + R_part2
// the new coef is (1-p0)*R_part1 + p0*R_part2 

// this function as 2 purposes: 
// 1. only care about q(t): log_size G1 values
// 2. care about the quotient poly coefficients: size/2 + size/4 +... + 1 = size-1 F values. Compactly represent it in one array. [empty, q_{dim-1}, q_{dim-2}, ..., q_0]. so that q_{i} is in [2^{dim-1-i}, 2^{dim-i})

// res should be allocated before calling
template <class T>
void multi_Q_coef_of_f(F*res, F*data, F*point, int dim, T**tvec_tower, const T&g, F external_multiplier=F_ONE, int data_size=-1)
{
    if (data_size < 0)
        data_size = 1 << dim;
    F *tmp = new F[1 << dim];
    memcpy(tmp, data, data_size * sizeof(F));
    for (int j = data_size; j<(1<<dim); j++)
    {
        tmp[j] = F_ZERO;
    }
    F *tmp_Q;
    int half_size;
    for (int j = 0; j < dim; j++)
    {
        half_size = 1 << (dim - 1 - j);
        tmp_Q = res + half_size;
        for (int i = 0; i < half_size; i++)
        {
            tmp_Q[i] = tmp[i + half_size] - tmp[i];
        }
        for (int i = 0; i < half_size; i++)
        {
            tmp[i] = tmp_Q[i] * point[j] + tmp[i];
        }
    }
    delete[] tmp;
}

template <class T>
void multi_Q_of_f(T*res, F*data, F*point, int dim, T**tvec_tower, const T&g, F external_multiplier=F_ONE, int data_size=-1)
{
    F*Q = new F[1<<dim];
    multi_Q_coef_of_f<T>(Q, data, point, dim, tvec_tower, g, external_multiplier, data_size);
    int half_size;
    for (int j = 0; j < dim; j++)
    {
        half_size = 1<<(dim-1-j);
        mulVec<T>(res[j], tvec_tower[j+1],  Q+half_size, half_size);
        res[j]*= external_multiplier;
    }
    delete[] Q;
}

bool MultiKZGVerify(const G1&f_com, F* point, F val, G1*proof, G2* ht, int dim, const G1&g, const G2&h); 

bool MultiKZGVerify(const G2&f_com, F* point, F val, G2*proof, G1* gt, int dim, const G2&h, const G1&g);

template <class T>
void compute_tvec_tower(T**tvec_tower, const T&g, F*tvec_beta, int dim)
{
    int tmp_size = 1<<dim;
    tvec_tower[0] = new T[tmp_size];
    for (int i = 0; i<tmp_size; i++)
    {
        tvec_tower[0][i] = g * tvec_beta[i];
    }
    for (int j = 1; j<=dim; j++)
    {
        tmp_size = 1<<(dim-j);
        tvec_tower[j] = new T[tmp_size];
        for(int i = 0; i < tmp_size; i++)
        {
            tvec_tower[j][i] = tvec_tower[j-1][i] + tvec_tower[j-1][i+tmp_size]; 
        }
    }
}

// G1 group 
// F*data and data_size fully describe the polynomial.


class MultiKZG{
public:    
    MultiKZG();
    void setup(int max_dim); // setup method 1: directly specify max_size
    void setup(int max_dim, const G1& g, const G2& h, F* tvec, G1**tvec_tower, G2*htvec); // method 2: reuse public parameters from elsewhere. 
    G1 commit(F*data, int data_dim, int data_size=-1); // by default data_size = 2^data_dim 
    void commit(G1&com, F*data, int data_dim, int data_size=-1); // requirement: data_size<=2^dim
    G1* prove(F*data, F*point, int data_dim, int data_size=-1, F external_multiplier=F_ONE); // prove at point.
    void prove(G1*proof, F*data, F*point, int data_dim, int data_size=-1, F external_multiplier=F_ONE); // prove at point.
    F eval(F*data, F*point, int data_dim, int data_size=-1); // eval at point.
    MultiKZGOpen<G1>* KZGopen(F*data, F*point, int data_dim, int data_size=-1); // open at point.
    void KZGopen(MultiKZGOpen<G1>*open_res, F*data, F*point, int data_dim, int data_size=-1); // open at point.
    void KZGopen_matrix(MultiKZGOpen<G1>*open_res, F**data, F*point_row, F*point_col, int row_dim, int col_dim, int row_size=-1, int col_size=-1); // open at point.
    bool verify(const G1&f_com, F*point, MultiKZGOpen<G1>*open); // verify at point.
    ~MultiKZG();
    bool verify(const G1&f_com, F*point, F val, G1*proof, int dim); 



public: 
    // public paramters 
    G1 g;
    G2 h; 
    int max_dim; 

    // verification key 
    G2* htvec; 

    // prove key
    G1** tvec_tower; // gtvec_tower[l][i] = g*beta(t[l:dim], i) // for efficiency, cut i. therefore, gbeta_t = gtvec_tower[0]

public: 
    F* tvec;
    bool local_setup; 

};


// G1 group 
// F*data and data_size fully describe the polynomial.
// we support any data_size <= 2^dim.
class MultiKZG_G2{
    public:    
        MultiKZG_G2();
        void setup(int max_dim); // setup method 1: directly specify max_size
        void setup(int max_dim, const G2& h, const G1& g, F* tvec, G2**tvec_tower, G1*gtvec); // method 2: reuse public parameters from elsewhere. 
        G2 commit(F*data, int data_dim, int data_size=-1); // data_dim <= max_dim
        void commit(G2&com, F*data, int data_dim, int data_size=-1); // 
        G2* prove(F*data, F*point, int data_dim, int data_size=-1, F external_multiplier=F_ONE); // prove at point.
        void prove(G2*proof, F*data, F*point, int data_dim, int data_size=-1, F external_multiplier=F_ONE); // prove at point.
        F eval(F*data, F*point, int data_dim, int data_size=-1); // eval at point.
        MultiKZGOpen<G2>* KZGopen(F*data, F*point, int data_dim, int data_size=-1); // open at point.
        void KZGopen(MultiKZGOpen<G2>*open_res, F*data, F*point, int data_dim, int data_size=-1); // open at point.
        void KZGopen_matrix(MultiKZGOpen<G2>*open_res, F**data, F*point_row, F*point_col, int row_dim, int col_dim, int row_size=-1, int col_size=-1); // open at point.
        bool verify(const G2&f_com, F*point, MultiKZGOpen<G2>*open); // verify at point.
        ~MultiKZG_G2();
        bool verify(const G2&f_com, F*point, F val, G2*proof, int dim); 
    
    
    
    public: 
        // public paramters 
        G1 g;
        G2 h; 
        int max_dim; 
    
        // verification key 
        G1* gtvec; 
    
        // prove key
        G2** tvec_tower; // gtvec_tower[l][i] = g*beta(t[l:dim], i) // for efficiency, cut i. therefore, gbeta_t = gtvec_tower[0]
    
    public: 
        F* tvec;
        bool local_setup; 
};