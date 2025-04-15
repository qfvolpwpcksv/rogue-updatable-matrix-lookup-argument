#include "gipa.hpp"

GIPP::GIPP()
{
    local_setup = false;
}

void GIPP::setup(int max_size, const G1 *g1p, const G2 *h2p, bool dummy)
{
    local_setup = true;
    this->max_size = max_size;

    hashAndMapToG2(this->mipp_h1, "random-mipp-h1");
    hashAndMapToG2(this->mipp_h2, "random-mipp-h2");
    hashAndMapToG1(this->mipp_g1, "random-mipp-g1");
    if (g1p != nullptr)
        this->g1 = *g1p;
    else
        hashAndMapToG1(this->g1, "random-g1");
    if (h2p != nullptr)
        this->h2 = *h2p;
    else
        hashAndMapToG2(this->h2, "random-h2");
    _alpha = F(rand());
    _beta = F(rand());

    pk_g1 = new G1[2 * max_size - 1];
    pk_h2 = new G2[2 * max_size - 1];
    ck_g1 = new G1[max_size];
    ck_h2 = new G2[max_size];

    if (dummy)
    {
        for (int i = 0; i < 2 * max_size - 1; i++)
        {
            pk_g1[i] = g1;
            pk_h2[i] = h2;
        }
        for (int i = 0; i < max_size; i++)
        {
            ck_g1[i] = g1;
            ck_h2[i] = h2;
        }
        vk_g_beta = g1;
        vk_h_alpha = h2;
    }
    else
    {
        G1 cum = g1;
        G2 cum2 = h2;
        for (int i = 0; i < 2 * max_size - 1; i++)
        {
            pk_g1[i] = cum;
            pk_h2[i] = cum2;
            cum *= _alpha;
            cum2 *= _beta;
        }
        for (int i = 0; i < max_size; i++)
        {
            ck_g1[i] = pk_g1[2 * i];
            ck_h2[i] = pk_h2[2 * i];
        }
        vk_g_beta = g1 * _beta;
        vk_h_alpha = h2 * _alpha;
    }
}

GIPP::~GIPP()
{
    if (!local_setup)
        return;
    delete[] pk_g1;
    delete[] pk_h2;
    delete[] ck_g1;
    delete[] ck_h2;
}

MIPP_Proof *GIPP::generate_proof(G1 *x, F *y, F rlc, int size)
{
    int log_size = int(ceil(log2(size)));
    MIPP_Proof *proof = new MIPP_Proof;
    proof->log_size = log_size;
    proof->r_c1 = F(rand());
    proof->r_c2 = F(rand());
    G2 h1_c1 = mipp_h1 * proof->r_c1;
    G2 h2_c2 = mipp_h2 * proof->r_c2;
    proof->cL = new GT[log_size];
    proof->cR = new GT[log_size];
    proof->r_challenges = new F[log_size];

    // rescaling by rlc:
    G1 *new_x = new G1[size];
    F *new_y = new F[size];
    G2 *new_ck1 = new G2[size];
    G1 *new_ck2 = new G1[size];
    G1vec_s_power(new_x, x, rlc * rlc, size);
    memcpy(new_y, y, size * sizeof(F));
    G2vec_s_power(new_ck1, ck_h2, F_ONE / (rlc * rlc), size);
    memcpy(new_ck2, ck_g1, size * sizeof(G1));
    proof->z = ip_F_G1(new_y, new_x, size);

    for (int i = 0; i < log_size; i++)
    {
        prove_single_round(proof, new_x, new_y, new_ck1, new_ck2, h1_c1, h2_c2, size >> i, i);
    }

    proof->final_ck1 = new_ck1[0];
    proof->final_ck2 = new_ck2[0];
    proof->final_x = new_x[0];
    proof->final_y = new_y[0];
    if (log_size >= 1)
        prove_final_ck1_T1_ck2_T2<G2, G1>(log_size, &proof->r_cha_ck1, &proof->ck1_val, &proof->proof_ck1, &proof->r_cha_ck2, &proof->ck2_val, &proof->proof_ck2, proof->r_challenges, rlc * rlc, true, true);

    delete[] new_x;
    delete[] new_y;
    delete[] new_ck1;
    delete[] new_ck2;
    return proof;
}

void GIPP::prove_single_round(MIPP_Proof *proof, G1 *x, F *y, G2 *ck1, G1 *ck2, G2 &h1_c1, G2 &h2_c2, int size, int round)
{
    int half_size = size / 2;
    G1 zL = ip_F_G1(y, x + half_size, half_size);          // zL = <x[m':], y[:m']>
    G1 zR = ip_F_G1(y + half_size, x, half_size);          // zR = <x[:m'], y[m':]>
    GT cL_x_com = ip_G1_G2(x + half_size, ck1, half_size); // com(ck1, x[m':])
    G1 cL_y_com = ip_F_G1(y, ck2 + half_size, half_size);  // com(ck2, y[:m'])
    GT cR_x_com = ip_G1_G2(x, ck1 + half_size, half_size); // com(ck1[m':], x[:m'])
    G1 cR_y_com = ip_F_G1(y + half_size, ck2, half_size);  // com(ck2[:m'], y[m':])
    GT cL_y_com_h, cR_y_com_h, zL_h, zR_h;
    millerLoop(cL_y_com_h, cL_y_com, h1_c1);
    millerLoop(cR_y_com_h, cR_y_com, h1_c1);
    millerLoop(zL_h, zL, h2_c2);
    millerLoop(zR_h, zR, h2_c2);
    proof->cL[round] = cL_x_com * cL_y_com_h * zL_h;
    proof->cR[round] = cR_x_com * cR_y_com_h * zR_h;

    F r_cha = non_zero_rand();
    proof->r_challenges[round] = r_cha;
    for (int i = 0; i < half_size; i++)
    {
        x[i] = x[i] + x[i + half_size] * r_cha;
        y[i] = y[i] + y[i + half_size] * (F_ONE / r_cha);
        ck1[i] = ck1[i] + ck1[i + half_size] * (F_ONE / r_cha);
        ck2[i] = ck2[i] + ck2[i + half_size] * r_cha;
    }
}

bool GIPP::verify_proof(MIPP_Proof *proof, GT x_com, G1 y_com, F rlc)
{
    bool ver_res = true;
    int log_size = proof->log_size;
    F r_cha;

    GT big_com, y_com_h, z_h; // original = X_com * e(y_com, h1) * e(z, h2)
    G2 h1_c1 = mipp_h1 * proof->r_c1;
    G2 h2_c2 = mipp_h2 * proof->r_c2;
    millerLoop(y_com_h, y_com, h1_c1);
    millerLoop(z_h, proof->z, h2_c2);
    big_com = x_com * y_com_h * z_h;
    GT cL_r, cR_rinv;
    for (int i = 0; i < log_size; i++)
    {
        r_cha = proof->r_challenges[i];
        if (r_cha == F_ZERO)
        {
            cout << "r_cha is zero" << endl;
            return false;
        }
        GT::pow(cL_r, proof->cL[i], r_cha);
        GT::pow(cR_rinv, proof->cR[i], F_ONE / r_cha);
        big_com = cL_r * cR_rinv * big_com;
    }
    // now x_com is the com of final_x; y_com is the com of final_y; z is the com of final_z.
    GT v_com_x, v_com_y, v_com_z, v_big_com;

    millerLoop(v_com_x, proof->final_x, proof->final_ck1);
    millerLoop(v_com_y, proof->final_ck2 * proof->final_y, h1_c1);
    G1 final_z = proof->final_x * proof->final_y;
    millerLoop(v_com_z, final_z, h2_c2);
    v_big_com = v_com_x * v_com_y * v_com_z;

    if (!pre_exp_GT_equal_check(big_com, v_big_com))
    {
        cout << "commitment of final x/y/z check fail" << endl;
        ver_res = false;
    }

    if (log_size == 0)
    {
        if (proof->final_ck1 == pk_h2[0] && proof->final_ck2 == pk_g1[0])
        {
            return ver_res;
        }
        else
        {
            cout << "final ck1 or ck2 check fail" << endl;
            return false;
        }
    }
    else
    {
        G2 ck1_l = proof->final_ck1 - (h2 * proof->ck1_val);
        G1 ck1_r = vk_g_beta - (g1 * proof->r_cha_ck1);
        G1 ck2_l = proof->final_ck2 - (g1 * proof->ck2_val);
        G2 ck2_r = vk_h_alpha - (h2 * proof->r_cha_ck2);
        if (!pairing_equal_check(g1, ck1_l, ck1_r, proof->proof_ck1))
        {
            std::cout << "final ck1 check fail" << endl;
            ver_res = false;
        }
        else if (!pairing_equal_check(ck2_l, h2, proof->proof_ck2, ck2_r))
        {
            std::cout << "final ck2 check fail" << endl;
            ver_res = false;
        }
    }
    return ver_res;
}

MIPP_Proof_k *GIPP::generate_proof_k(G1 *x, F *y_gen, F rlc, int size, bool y_is_beta)
{
    int log_size = int(ceil(log2(size)));
    MIPP_Proof_k *proof = new MIPP_Proof_k;
    proof->log_size = log_size;
    proof->r_c = F(rand());
    G2 h_c = mipp_h2 * proof->r_c;
    proof->cL = new GT[log_size];
    proof->cR = new GT[log_size];
    proof->r_challenges = new F[log_size];

    // rescaling by rlc:

    G1 *new_x = new G1[size];
    G1vec_s_power(new_x, x, rlc * rlc, size);
    F *new_y = new F[size];
    if (y_is_beta)
    {
        beta_fullvec(new_y, y_gen, log_size);
    }
    else
        s_powers(new_y, *y_gen, size);

    G2 *new_ck1 = new G2[size];
    G2vec_s_power(new_ck1, ck_h2, F_ONE / (rlc * rlc), size);
    F *new_ck2 = new F[size];
    for (int i = 0; i < size; i++)
        new_ck2[i] = F_ONE;
    proof->z = ip_F_G1(new_y, new_x, size);

    for (int i = 0; i < log_size; i++)
    {
        prove_single_round_k(proof, new_x, new_y, new_ck1, new_ck2, h_c, size >> i, i);
    }

    proof->final_ck1 = new_ck1[0];
    proof->final_x = new_x[0];

    if (log_size >= 1)
        prove_final_ck1_T1_ck2_T2<G2, G1>(log_size, &proof->r_cha_ck1, &proof->ck1_val, &proof->proof_ck1, nullptr, nullptr, nullptr, proof->r_challenges, rlc * rlc, true, false);

    delete[] new_x;
    delete[] new_y;
    delete[] new_ck1;
    delete[] new_ck2;

    return proof;
}

int size_of_mipp_k(int row_n)
{
    int log_size = int(ceil(log2(row_n)));
    int size_of_mipp = sizeof(G1) * 2 + sizeof(F) + sizeof(GT *) * 2 + sizeof(F *) + sizeof(G2) + sizeof(int) + sizeof(F) * 2 + sizeof(G2);
    return size_of_mipp + sizeof(GT) * log_size * 2 + sizeof(F) * log_size;
}

void GIPP::prove_single_round_k(MIPP_Proof_k *proof, G1 *x, F *y, G2 *ck1, F *ck2, G2 &h_c, int size, int round)
{
    int half_size = size / 2;
    G1 zL = ip_F_G1(y, x + half_size, half_size);          // zL = <x[m':], y[:m']>
    G1 zR = ip_F_G1(y + half_size, x, half_size);          // zR = <x[:m'], y[m':]>
    GT cL_x_com = ip_G1_G2(x + half_size, ck1, half_size); // com(ck1, x[m':])
    GT cR_x_com = ip_G1_G2(x, ck1 + half_size, half_size); // com(ck1[m':], x[:m'])
    GT zL_h, zR_h;
    millerLoop(zL_h, zL, h_c);
    millerLoop(zR_h, zR, h_c);
    proof->cL[round] = cL_x_com * zL_h;
    proof->cR[round] = cR_x_com * zR_h;

    F r_cha = non_zero_rand();
    proof->r_challenges[round] = r_cha;
    for (int i = 0; i < half_size; i++)
    {
        x[i] = x[i] + x[i + half_size] * r_cha;
        y[i] = y[i] + y[i + half_size] * (F_ONE / r_cha);
        ck1[i] = ck1[i] + ck1[i + half_size] * (F_ONE / r_cha);
        ck2[i] = ck2[i] + ck2[i + half_size] * r_cha;
    }
}

bool GIPP::verify_proof_k(MIPP_Proof_k *proof, GT x_com, F *y_gen, F rlc, bool y_is_beta)
{
    bool ver_res = true;
    int log_size = proof->log_size;
    F r_cha;

    GT big_com, z_h; // original = X_com * e(z, h2)
    G2 h_c = mipp_h2 * proof->r_c;
    millerLoop(z_h, proof->z, h_c);
    big_com = x_com * z_h;
    GT cL_r, cR_rinv;

    for (int i = 0; i < log_size; i++)
    {
        r_cha = proof->r_challenges[i];
        if (r_cha == F_ZERO)
        {
            cout << "r_cha is zero" << endl;
            return false;
        }
        GT::pow(cL_r, proof->cL[i], r_cha);
        GT::pow(cR_rinv, proof->cR[i], F_ONE / r_cha);
        big_com = cL_r * cR_rinv * big_com;
    }

    GT v_com_x, v_com_z, v_big_com;
    millerLoop(v_com_x, proof->final_x, proof->final_ck1);

    F final_y = F_ONE;
    if (y_is_beta)
    {
        for (int i = 0; i < log_size; i++)
        {
            final_y *= (1 - y_gen[i] + y_gen[i] / proof->r_challenges[i]);
        }
    }
    else
    {
        F y_power = y_gen[0];
        for (int i = 0; i < log_size; i++)
        {
            final_y *= (1 + y_power / proof->r_challenges[log_size - 1 - i]);
            y_power *= y_power;
        }
    }
    G1 final_z = proof->final_x * final_y;
    millerLoop(v_com_z, final_z, h_c);
    v_big_com = v_com_x * v_com_z;
    if (!pre_exp_GT_equal_check(big_com, v_big_com))
    {
        cout << "commitment of final x/z check fail" << endl;
        ver_res = false;
    }

    if (log_size == 0)
    {
        if (proof->final_ck1 == pk_h2[0])
        {
            return ver_res;
        }
        {
            ver_res = false;
        }
    }
    else
    {
        G2 ck1_l = proof->final_ck1 - (h2 * proof->ck1_val);
        G1 ck1_r = vk_g_beta - g1 * proof->r_cha_ck1;
        if (!pairing_equal_check(g1, ck1_l, ck1_r, proof->proof_ck1))
        {
            std::cout << "final ck1 check fail" << endl;
            ver_res = false;
        }
    }

    return ver_res;
}

MIPP_Proof_k_G2 *GIPP::generate_proof_k_G2(G2 *x, F *y_gen, F rlc, int size, bool y_is_beta)
{
    int log_size = int(ceil(log2(size)));
    MIPP_Proof_k_G2 *proof = new MIPP_Proof_k_G2;
    proof->log_size = log_size;
    proof->r_c = F(rand());
    G1 g_c = mipp_g1 * proof->r_c;
    proof->cL = new GT[log_size];
    proof->cR = new GT[log_size];
    proof->r_challenges = new F[log_size];

    // rescaling by rlc:
    G2 *new_x = new G2[size];
    G2vec_s_power(new_x, x, rlc * rlc, size);
    F *new_y = new F[size];
    if (y_is_beta)
    {
        beta_fullvec(new_y, y_gen, log_size);
    }
    else
        s_powers(new_y, *y_gen, size);

    G1 *new_ck1 = new G1[size];
    G1vec_s_power(new_ck1, ck_g1, F_ONE / (rlc * rlc), size);
    F *new_ck2 = new F[size];
    for (int i = 0; i < size; i++)
    {
        new_ck2[i] = F_ONE;
    }
    proof->z = ip_F_G2(new_y, new_x, size);

    for (int i = 0; i < log_size; i++)
    {
        prove_single_round_k_G2(proof, new_x, new_y, new_ck1, new_ck2, g_c, size >> i, i);
    }

    proof->final_ck1 = new_ck1[0];
    proof->final_x = new_x[0];
    if (log_size >= 1)
    {
        prove_final_ck1_T1_ck2_T2<G1, G1>(log_size, &proof->r_cha_ck1, &proof->ck1_val, &proof->proof_ck1, nullptr, nullptr, nullptr, proof->r_challenges, rlc * rlc, true, false);
    }

    delete[] new_x;
    delete[] new_y;
    delete[] new_ck1;
    delete[] new_ck2;
    return proof;
}

void GIPP::prove_single_round_k_G2(MIPP_Proof_k_G2 *proof, G2 *x, F *y, G1 *ck1, F *ck2, G1 &g_c, int size, int round)
{
    int half_size = size / 2;
    G2 zL = ip_F_G2(y, x + half_size, half_size);          // zL = <x[m':], y[:m']>
    G2 zR = ip_F_G2(y + half_size, x, half_size);          // zR = <x[:m'], y[m':]>
    GT cL_x_com = ip_G1_G2(ck1, x + half_size, half_size); // com(ck1, x[m':])
    GT cR_x_com = ip_G1_G2(ck1 + half_size, x, half_size); // com(ck1[m':], x[:m'])
    GT zL_h, zR_h;
    millerLoop(zL_h, g_c, zL);
    millerLoop(zR_h, g_c, zR);
    proof->cL[round] = cL_x_com * zL_h;
    proof->cR[round] = cR_x_com * zR_h;

    F r_cha = non_zero_rand();
    proof->r_challenges[round] = r_cha;
    for (int i = 0; i < half_size; i++)
    {
        x[i] = x[i] + x[i + half_size] * r_cha;
        y[i] = y[i] + y[i + half_size] * (F_ONE / r_cha);
        ck1[i] = ck1[i] + ck1[i + half_size] * (F_ONE / r_cha);
        ck2[i] = ck2[i] + ck2[i + half_size] * r_cha;
    }
}

bool GIPP::verify_proof_k_G2(MIPP_Proof_k_G2 *proof, GT x_com, F *y_gen, F rlc, bool y_is_beta)
{
    bool ver_res = true;
    int log_size = proof->log_size;
    F r_cha;

    GT big_com, z_h;
    G1 g_c = mipp_g1 * proof->r_c;
    millerLoop(z_h, g_c, proof->z);
    big_com = x_com * z_h;
    GT cL_r, cR_rinv;

    for (int i = 0; i < log_size; i++)
    {
        r_cha = proof->r_challenges[i];
        if (r_cha == F_ZERO)
        {
            cout << "r_cha is zero" << endl;
            return false;
        }
        GT::pow(cL_r, proof->cL[i], r_cha);
        GT::pow(cR_rinv, proof->cR[i], F_ONE / r_cha);
        big_com = cL_r * cR_rinv * big_com;
    }

    GT v_com_x, v_com_z, v_big_com;
    millerLoop(v_com_x, proof->final_ck1, proof->final_x);

    F final_y = F_ONE;
    if (y_is_beta)
    {
        for (int i = 0; i < log_size; i++)
        {
            final_y *= (1 - y_gen[i] + y_gen[i] / proof->r_challenges[i]);
        }
    }
    else
    {
        F y_power = y_gen[0];
        for (int i = 0; i < log_size; i++)
        {
            final_y *= (1 + y_power / proof->r_challenges[log_size - 1 - i]);
            y_power *= y_power;
        }
    }

    G2 final_z = proof->final_x * final_y;
    millerLoop(v_com_z, g_c, final_z);
    v_big_com = v_com_x * v_com_z;
    if (!pre_exp_GT_equal_check(big_com, v_big_com))
    {
        cout << "commitment of final x/z check fail" << endl;
        ver_res = false;
    }

    if (log_size == 0)
    {
        if (proof->final_ck1 == pk_g1[0])
        {
            return ver_res;
        }
        else
        {
            cout << "final ck1 check fail" << endl;
            return false;
        }
    }
    else
    {
        G1 ck1_l = proof->final_ck1 - (g1 * proof->ck1_val);
        G2 ck1_r = vk_h_alpha - h2 * proof->r_cha_ck1;
        if (!pairing_equal_check(ck1_l, h2, proof->proof_ck1, ck1_r))
        {
            std::cout << "final ck1 check fail" << endl;
            ver_res = false;
        }
    }

    return ver_res;
}

IPA_Proof *GIPP::generate_proof_ipa(F *x, F *y, F rlc, int size)
{
    int log_size = int(ceil(log2(size)));
    IPA_Proof *proof = new IPA_Proof;
    proof->log_size = log_size;
    proof->r_c2 = F(rand());
    proof->r_cz = F(rand());
    G1 g1_cz = mipp_g1 * proof->r_cz;

    proof->cL = new G1[log_size];
    proof->cR = new G1[log_size];
    proof->r_challenges = new F[log_size];

    // rescaling by rlc:

    F *new_x = new F[size];
    Fvec_s_power(new_x, x, rlc * rlc, size);
    F *new_y = new F[size];
    memcpy(new_y, y, size * sizeof(F));
    G1 *new_ck1 = new G1[size];
    G1vec_s_power(new_ck1, ck_g1, F_ONE / (rlc * rlc), size);
    G1 *new_ck2 = new G1[size];
    memcpy(new_ck2, ck_g1, size * sizeof(G1));
    proof->z = ip_F_F(new_y, new_x, size);

    for (int i = 0; i < log_size; i++)
    {
        prove_single_round_ipa(proof, new_x, new_y, new_ck1, new_ck2, proof->r_c2, g1_cz, size >> i, i);
    }

    proof->final_ck1 = new_ck1[0];
    proof->final_ck2 = new_ck2[0];
    proof->final_x = new_x[0];
    proof->final_y = new_y[0];

    if (log_size >= 1)
        prove_final_ck1_T1_ck2_T2<G1, G1>(log_size, &proof->r_cha_ck1, &proof->ck1_val, &proof->proof_ck1, &proof->r_cha_ck2, &proof->ck2_val, &proof->proof_ck2, proof->r_challenges, rlc * rlc, true, true);

    delete[] new_x;
    delete[] new_y;
    delete[] new_ck1;
    delete[] new_ck2;
    return proof;
}

void GIPP::prove_single_round_ipa(IPA_Proof *proof, F *x, F *y, G1 *ck1, G1 *ck2, F &r_c2, G1 &g1_cz, int size, int round)
{
    int half_size = size / 2;
    F zL = ip_F_F(y, x + half_size, half_size);           // zL = <x[m':], y[:m']>
    F zR = ip_F_F(y + half_size, x, half_size);           // zR = <x[:m'], y[m':]>
    G1 cL_x_com = ip_F_G1(x + half_size, ck1, half_size); // com(ck1, x[m':])
    G1 cL_y_com = ip_F_G1(y, ck2 + half_size, half_size); // com(ck2, y[:m'])
    G1 cR_x_com = ip_F_G1(x, ck1 + half_size, half_size); // com(ck1[m':], x[:m'])
    G1 cR_y_com = ip_F_G1(y + half_size, ck2, half_size); // com(ck2[:m'], y[m':])
    proof->cL[round] = cL_x_com + cL_y_com * r_c2 + g1_cz * zL;
    proof->cR[round] = cR_x_com + cR_y_com * r_c2 + g1_cz * zR;

    F r_cha = non_zero_rand();
    proof->r_challenges[round] = r_cha;
    for (int i = 0; i < half_size; i++)
    {
        x[i] = x[i] + x[i + half_size] * r_cha;
        y[i] = y[i] + y[i + half_size] * (F_ONE / r_cha);
        ck1[i] = ck1[i] + ck1[i + half_size] * (F_ONE / r_cha);
        ck2[i] = ck2[i] + ck2[i + half_size] * r_cha;
    }
}

bool GIPP::verify_proof_ipa(IPA_Proof *proof, G1 x_com, G1 y_com, F rlc)
{
    bool ver_res = true;
    int log_size = proof->log_size;
    F r_cha;

    G1 g1_cz = mipp_g1 * proof->r_cz;
    G1 big_com = x_com + y_com * proof->r_c2 + g1_cz * proof->z;

    for (int i = 0; i < log_size; i++)
    {
        r_cha = proof->r_challenges[i];
        if (r_cha == F_ZERO)
        {
            cout << "r_cha is zero" << endl;
            return false;
        }
        big_com = big_com + proof->cL[i] * r_cha + proof->cR[i] * (F_ONE / r_cha);
    }
    F final_z = proof->final_x * proof->final_y;
    G1 final_big_com = proof->final_ck1 * proof->final_x +
                       proof->final_ck2 * proof->final_y * proof->r_c2 +
                       g1_cz * final_z;
    if (big_com != final_big_com)
    {
        cout << "big com of final x/y/z check fail" << endl;
        ver_res = false;
    }
    if (log_size == 0)
    {
        if (proof->final_ck1 == pk_g1[0] && proof->final_ck2 == pk_g1[0])
        {
            return ver_res;
        }
        {
            ver_res = false;
        }
    }
    else
    {
        G1 ck1_l = proof->final_ck1 - (g1 * proof->ck1_val);
        G1 ck2_l = proof->final_ck2 - (g1 * proof->ck2_val);
        G2 ck1_r = vk_h_alpha - (h2 * proof->r_cha_ck1);
        G2 ck2_r = vk_h_alpha - (h2 * proof->r_cha_ck2);
        if (!pairing_equal_check(ck1_l, h2, proof->proof_ck1, ck1_r))
        {
            std::cout << "final ck1 check fail" << endl;
            ver_res = false;
        }
        else if (!pairing_equal_check(ck2_l, h2, proof->proof_ck2, ck2_r))
        {
            std::cout << "final ck2 check fail" << endl;
            ver_res = false;
        }
    }
    return ver_res;
}

BatchedIPA_Proof *GIPP::generate_proof_batched_ipa(F **x, F **y, F rlc, int size, int proof_num)
{
    BatchedIPA_Proof *proof = new BatchedIPA_Proof;
    proof->proof_num = proof_num;
    proof->rand_a = new F[proof_num];
    for (int l = 0; l < proof_num; l++)
    {
        proof->rand_a[l] = F(rand());
    }
    int log_size = int(ceil(log2(size)));
    proof->log_size = log_size;
    assert(size == 1 << log_size);
    proof->r_c2 = F(rand());
    proof->r_cz = F(rand());
    G1 g1_cz = mipp_g1 * proof->r_cz;

    proof->cL = new G1[log_size];
    proof->cR = new G1[log_size];
    proof->r_challenges = new F[log_size];

    // rescaling by rlc
    F rlc_sq = rlc * rlc;
    F **new_x = new F *[proof_num];
    F **new_y = new F *[proof_num];
    for (int l = 0; l < proof_num; l++)
    {
        new_x[l] = new F[size];
        new_y[l] = new F[size];
        Fvec_s_power(new_x[l], x[l], rlc_sq, size);
        memcpy(new_y[l], y[l], size * sizeof(F));
    }
    G1 *new_ck1 = new G1[size];
    G1 *new_ck2 = new G1[size];
    G1vec_s_power(new_ck1, ck_g1, F_ONE / rlc_sq, size);
    memcpy(new_ck2, ck_g1, size * sizeof(G1));

    proof->z = new F[proof_num];
    proof->final_x = new F[proof_num];
    proof->final_y = new F[proof_num];
    for (int l = 0; l < proof_num; l++)
    {
        proof->z[l] = ip_F_F(new_y[l], new_x[l], size);
    }

    for (int round = 0; round < log_size; round++)
    {
        prove_single_round_batched_ipa(proof, new_x, new_y, new_ck1, new_ck2, proof->r_c2, g1_cz, size >> round, round, proof_num);
    }

    proof->final_ck1 = new_ck1[0];
    proof->final_ck2 = new_ck2[0];
    for (int l = 0; l < proof_num; l++)
    {
        proof->final_x[l] = new_x[l][0];
        proof->final_y[l] = new_y[l][0];
    }

    if (log_size >= 1)
    {
        prove_final_ck1_T1_ck2_T2<G1, G1>(log_size, &proof->r_cha_ck1, &proof->ck1_val, &proof->proof_ck1, &proof->r_cha_ck2, &proof->ck2_val, &proof->proof_ck2, proof->r_challenges, rlc_sq, true, true);
    }

    for (int l = 0; l < proof_num; l++)
    {
        delete[] new_x[l];
        delete[] new_y[l];
    }
    delete[] new_x;
    delete[] new_y;
    delete[] new_ck1;
    delete[] new_ck2;
    return proof;
}

void GIPP::prove_single_round_batched_ipa(BatchedIPA_Proof *proof, F **x, F **y, G1 *ck1, G1 *ck2, F &r_c2, G1 &g1_cz, int size, int round, int proof_num)
{
    int half_size = size / 2;
    F *zL = new F[proof_num];
    F *zR = new F[proof_num];

    F *x_aggregated = new F[size + proof_num];
    F *y_aggregated = new F[size + proof_num];
    F *x_tmp = x_aggregated + size;
    F *y_tmp = y_aggregated + size;

    for (int i = 0; i < size; i++)
    {
        for (int l = 0; l < proof_num; l++)
        {
            x_tmp[l] = x[l][i];
            y_tmp[l] = y[l][i];
        }
        x_aggregated[i] = ip_F_F(proof->rand_a, x_tmp, proof_num);
        y_aggregated[i] = ip_F_F(proof->rand_a, y_tmp, proof_num);
    }

    for (int l = 0; l < proof_num; l++)
    {
        zL[l] = ip_F_F(y[l], x[l] + half_size, half_size);
        zR[l] = ip_F_F(y[l] + half_size, x[l], half_size);
    }
    G1 cL_x_com = ip_F_G1(x_aggregated + half_size, ck1, half_size);
    G1 cL_y_com = ip_F_G1(y_aggregated, ck2 + half_size, half_size);
    G1 cR_x_com = ip_F_G1(x_aggregated, ck1 + half_size, half_size);
    G1 cR_y_com = ip_F_G1(y_aggregated + half_size, ck2, half_size);
    proof->cL[round] = cL_x_com + cL_y_com * r_c2 + g1_cz * ip_F_F(proof->rand_a, zL, proof_num);
    proof->cR[round] = cR_x_com + cR_y_com * r_c2 + g1_cz * ip_F_F(proof->rand_a, zR, proof_num);
    delete[] x_aggregated;
    delete[] y_aggregated;
    delete[] zL;
    delete[] zR;

    F r_cha = non_zero_rand();
    proof->r_challenges[round] = r_cha;

    for (int i = 0; i < half_size; i++)
    {
        for (int l = 0; l < proof_num; l++)
        {
            x[l][i] = x[l][i] + x[l][i + half_size] * r_cha;
            y[l][i] = y[l][i] + y[l][i + half_size] * (F_ONE / r_cha);
        }
        ck1[i] = ck1[i] + ck1[i + half_size] * (F_ONE / r_cha);
        ck2[i] = ck2[i] + ck2[i + half_size] * r_cha;
    }
}

bool GIPP::verify_proof_batched_ipa(BatchedIPA_Proof *proof, G1 *x_com, G1 *y_com, F rlc, int proof_num)
{
    bool ver_res = true;
    int log_size = proof->log_size;
    F r_cha;

    G1 g1_cz = mipp_g1 * proof->r_cz;

    F aggregated_z = ip_F_F(proof->rand_a, proof->z, proof_num);
    F aggregated_final_x = ip_F_F(proof->rand_a, proof->final_x, proof_num);
    F aggregated_final_y = ip_F_F(proof->rand_a, proof->final_y, proof_num);
    G1 aggregated_x_com = ip_F_G1(proof->rand_a, x_com, proof_num);
    G1 aggregated_y_com = ip_F_G1(proof->rand_a, y_com, proof_num);

    G1 big_com = aggregated_x_com + aggregated_y_com * proof->r_c2 + g1_cz * aggregated_z;
    for (int i = 0; i < log_size; i++)
    {
        r_cha = proof->r_challenges[i];
        if (r_cha == F_ZERO)
        {
            cout << "r_cha is zero" << endl;
            return false;
        }
        big_com = big_com + proof->cL[i] * r_cha + proof->cR[i] * (F_ONE / r_cha);
    }
    F final_z = F_ZERO;
    for (int l = 0; l < proof_num; l++)
    {
        final_z += proof->final_x[l] * proof->final_y[l] * proof->rand_a[l];
    }
    G1 final_big_com = proof->final_ck1 * aggregated_final_x +
                       proof->final_ck2 * aggregated_final_y * proof->r_c2 +
                       g1_cz * final_z;
    if (big_com != final_big_com)
    {
        cout << "big com of final x/y/z check fail" << endl;
        // return false;
        ver_res = false;
    }
    if (log_size == 0)
    {
        if (proof->final_ck1 == pk_g1[0] && proof->final_ck2 == pk_g1[0])
        {
            return ver_res;
        }
        {
            ver_res = false;
        }
    }
    else
    {
        G1 ck1_l = proof->final_ck1 - (g1 * proof->ck1_val);
        G1 ck2_l = proof->final_ck2 - (g1 * proof->ck2_val);
        G2 ck1_r = vk_h_alpha - (h2 * proof->r_cha_ck1);
        G2 ck2_r = vk_h_alpha - (h2 * proof->r_cha_ck2);
        if (!pairing_equal_check(ck1_l, h2, proof->proof_ck1, ck1_r))
        {
            std::cout << "final ck1 check fail" << endl;
            // return false;
            ver_res = false;
        }
        else if (!pairing_equal_check(ck2_l, h2, proof->proof_ck2, ck2_r))
        {
            std::cout << "final ck2 check fail" << endl;
            // return false;
            ver_res = false;
        }
    }
    // return true;
    return ver_res;
}

TIPP_Proof *GIPP::generate_proof_tipp(G1 *x, G2 *y, F rlc, int size, GT *z_precom)
{
    int log_size = int(ceil(log2(size)));
    TIPP_Proof *proof = new TIPP_Proof;

    proof->cL_x_coms = new GT[log_size];
    proof->cR_x_coms = new GT[log_size];
    proof->cL_y_coms = new GT[log_size];
    proof->cR_y_coms = new GT[log_size];
    proof->zLs = new GT[log_size];
    proof->zRs = new GT[log_size];
    proof->r_challenges = new F[log_size];
    proof->log_size = log_size;

    // rescaling by rlc:

    G1 *new_x = new G1[size];
    G1vec_s_power(new_x, x, rlc * rlc, size);
    G2 *new_y = new G2[size];
    memcpy(new_y, y, size * sizeof(G2));
    G2 *new_ck1 = new G2[size];
    G2vec_s_power(new_ck1, ck_h2, F_ONE / (rlc * rlc), size);
    G1 *new_ck2 = new G1[size];
    memcpy(new_ck2, ck_g1, size * sizeof(G1));

    if (z_precom == nullptr)
        proof->z = ip_G1_G2(new_x, new_y, size);
    else
        proof->z = *z_precom;
    for (int i = 0; i < log_size; i++)
    {
        prove_single_round_tipp(proof, new_x, new_y, new_ck1, new_ck2, size >> i, i);
    }

    // now its the final one.

    proof->final_x = new_x[0];
    proof->final_y = new_y[0];
    proof->final_ck1 = new_ck1[0];
    proof->final_ck2 = new_ck2[0];

    if (log_size >= 1)
        prove_final_ck1_T1_ck2_T2<G2, G1>(log_size, &proof->r_cha_ck1, &proof->ck1_val, &proof->proof_ck1, &proof->r_cha_ck2, &proof->ck2_val, &proof->proof_ck2, proof->r_challenges, rlc * rlc, true, true);

    delete[] new_x;
    delete[] new_y;
    delete[] new_ck1;
    delete[] new_ck2;
    return proof;
}

void GIPP::prove_single_round_tipp(TIPP_Proof *proof, G1 *x, G2 *y, G2 *ck1, G1 *ck2, int size, int round)
{
    int half_size = size / 2;
    proof->cL_x_coms[round] = ip_G1_G2(x + half_size, ck1, half_size); // com(ck1, x[m':])
    proof->cL_y_coms[round] = ip_G1_G2(ck2 + half_size, y, half_size); // com(ck2, y[:m'])
    proof->cR_x_coms[round] = ip_G1_G2(x, ck1 + half_size, half_size); // com(ck1[m':], x[:m'])
    proof->cR_y_coms[round] = ip_G1_G2(ck2, y + half_size, half_size); // com(ck2[:m'], y[m':])
    proof->zLs[round] = ip_G1_G2(x + half_size, y, half_size);
    proof->zRs[round] = ip_G1_G2(x, y + half_size, half_size);

    F r_cha = non_zero_rand();
    // F r_cha = F_ONE;
    proof->r_challenges[round] = r_cha;
    for (int i = 0; i < half_size; i++)
    {
        x[i] = x[i] + x[i + half_size] * r_cha;
        y[i] = y[i] + y[i + half_size] * (F_ONE / r_cha);
        ck1[i] = ck1[i] + ck1[i + half_size] * (F_ONE / r_cha);
        ck2[i] = ck2[i] + ck2[i + half_size] * r_cha;
    }
}

bool GIPP::verify_proof_tipp(TIPP_Proof *proof, GT x_com, GT y_com, F rlc)
{
    bool ver_res = true;
    int log_size = proof->log_size;
    GT z = proof->z;
    GT cL_x_com_r;
    GT cL_y_com_r;
    GT cR_x_com_rinv;
    GT cR_y_com_rinv;
    GT zL_r;
    GT zR_r;

    F r_cha;
    for (int i = 0; i < log_size; i++)
    {
        r_cha = proof->r_challenges[i];
        if (r_cha == F_ZERO)
        {
            cout << "r_cha is zero" << endl;
            return false;
        }
        GT::pow(cL_x_com_r, proof->cL_x_coms[i], r_cha);
        GT::pow(cL_y_com_r, proof->cL_y_coms[i], r_cha);
        GT::pow(cR_x_com_rinv, proof->cR_x_coms[i], F_ONE / r_cha);
        GT::pow(cR_y_com_rinv, proof->cR_y_coms[i], F_ONE / r_cha);
        GT::pow(zL_r, proof->zLs[i], r_cha);
        GT::pow(zR_r, proof->zRs[i], F_ONE / r_cha);
        x_com = cL_x_com_r * cR_x_com_rinv * x_com;
        y_com = cL_y_com_r * cR_y_com_rinv * y_com;
        z = zL_r * zR_r * z;
    }
    // now x_com is the com of final_x; y_com is the com of final_y; z is the com of final_z.
    GT v_com_x;
    GT v_com_y;
    millerLoop(v_com_x, proof->final_x, proof->final_ck1);
    millerLoop(v_com_y, proof->final_ck2, proof->final_y);
    finalExp(v_com_x, v_com_x);
    finalExp(v_com_y, v_com_y);
    finalExp(x_com, x_com);
    finalExp(y_com, y_com);
    if (v_com_x != x_com || v_com_y != y_com)
    {
        cout << "commitment of final x/y check fail" << endl;
        ver_res = false;
    }
    GT xy;
    millerLoop(xy, proof->final_x, proof->final_y);
    finalExp(xy, xy);
    finalExp(z, z);
    if (xy != z)
    {
        cout << "final z=xy check fail" << endl;
        ver_res = false;
    }

    // check well-formedness of the final commitment key

    if (log_size == 0)
    {
        if (!(proof->final_ck1 == pk_h2[0] && proof->final_ck2 == pk_g1[0]))
            ver_res = false;
        return ver_res;
    }
    else
    {
        // check e(final_ck2/g^{ck2_val}}, h2) = e(pi_ck2, h^alpha / h^z)
        // check e(g, final_ck1/h^{ck1_val}) = e(g^beta/g^z, pi_ck1)

        G2 ck1_l = proof->final_ck1 - (h2 * proof->ck1_val);
        G1 ck1_r = vk_g_beta - g1 * proof->r_cha_ck1;
        G1 ck2_l = proof->final_ck2 - (g1 * proof->ck2_val);
        G2 ck2_r = vk_h_alpha - h2 * proof->r_cha_ck2;
        if (!pairing_equal_check(g1, ck1_l, ck1_r, proof->proof_ck1))
        {
            std::cout << "final ck1 check fail" << endl;
            ver_res = false;
        }
        else if (!pairing_equal_check(ck2_l, h2, proof->proof_ck2, ck2_r))
        {
            std::cout << "final ck2 check fail" << endl;
            ver_res = false;
        }
    }
    return ver_res;
}

// Batched TIPP
BatchedTIPP_Proof *GIPP::generate_proof_batched_tipp(G1 **x, G2 **y, F rlc, int size, int proof_num, BatchTIPP_Aux *aux)
{
    BatchedTIPP_Proof *proof = new BatchedTIPP_Proof;
    proof->proof_num = proof_num;
    proof->rand_a = new F[proof_num];
    for (int l = 0; l < proof_num; l++)
    {
        proof->rand_a[l] = F(rand());
    }
    int log_size = int(ceil(log2(size)));
    assert(size == 1 << log_size);
    proof->log_size = log_size;

    proof->cL_x_coms = new GT[log_size];
    proof->cR_x_coms = new GT[log_size];
    proof->cL_y_coms = new GT[log_size];
    proof->cR_y_coms = new GT[log_size];
    proof->zLs = new GT *[log_size];
    proof->zRs = new GT *[log_size];
    for (int r = 0; r < log_size; r++)
    {
        proof->zLs[r] = new GT[proof_num]; // to faciltate batching across proof_num.
        proof->zRs[r] = new GT[proof_num];
    }
    proof->r_challenges = new F[log_size];

    // rescale by rlc
    F rlc_sq = rlc * rlc;
    G1 **new_x = new G1 *[proof_num];
    G2 **new_y = new G2 *[proof_num];
    G2 *new_ck1 = new G2[size];
    G1 *new_ck2 = new G1[size];
    proof->z = new GT[proof_num];
    proof->final_x = new G1[proof_num];
    proof->final_y = new G2[proof_num];

    for (int l = 0; l < proof_num; l++)
    {
        new_x[l] = new G1[size];
        G1vec_s_power(new_x[l], x[l], rlc_sq, size);
        new_y[l] = new G2[size];
        memcpy(new_y[l], y[l], size * sizeof(G2));
        if (aux == nullptr || aux->z == nullptr)
            proof->z[l] = ip_G1_G2(new_x[l], new_y[l], size);
        else
            proof->z[l] = aux->z[l];
    }

    G2vec_s_power(new_ck1, ck_h2, F_ONE / rlc_sq, size);
    memcpy(new_ck2, ck_g1, size * sizeof(G1));

    for (int round = 0; round < log_size; round++)
    {
        prove_single_round_batched_tipp(proof, new_x, new_y, new_ck1, new_ck2, size >> round, round, proof_num, aux);
    }
    for (int l = 0; l < proof_num; l++)
    {
        proof->final_x[l] = new_x[l][0];
        proof->final_y[l] = new_y[l][0];
    }
    proof->final_ck1 = new_ck1[0];
    proof->final_ck2 = new_ck2[0];

    if (log_size >= 1)
    {
        prove_final_ck1_T1_ck2_T2<G2, G1>(log_size, &proof->r_cha_ck1, &proof->ck1_val, &proof->proof_ck1, &proof->r_cha_ck2, &proof->ck2_val, &proof->proof_ck2, proof->r_challenges, rlc_sq, true, true);
    }

    // delete
    for (int l = 0; l < proof_num; l++)
    {
        delete[] new_x[l];
        delete[] new_y[l];
    }
    delete[] new_x;
    delete[] new_y;
    delete[] new_ck1;
    delete[] new_ck2;
    return proof;
}

void GIPP::prove_single_round_batched_tipp(BatchedTIPP_Proof *proof, G1 **x, G2 **y, G2 *ck1, G1 *ck2, int size, int round, int proof_num, BatchTIPP_Aux *aux)
{
    int half_size = size / 2;
    if (round == 0 && aux != nullptr)
    {
        for (int l = 0; l < proof_num; l++)
        {
            if (aux->zL_0 != nullptr)
                proof->zLs[round][l] = aux->zL_0[l];
            if (aux->zR_0 != nullptr)
                proof->zRs[round][l] = aux->zR_0[l];
        }
    }
    else
    {
        for (int l = 0; l < proof_num; l++)
        {
            proof->zLs[round][l] = ip_G1_G2(x[l] + half_size, y[l], half_size); // com(ck1, x[m':])
            proof->zRs[round][l] = ip_G1_G2(x[l], y[l] + half_size, half_size); // com(ck1[m':], x[:m'])
        }
    }
    // compute aggregated x[round] and y[round]
    G1 *x_aggregated = new G1[size + proof_num];
    G2 *y_aggregated = new G2[size + proof_num];
    G1 *x_tmp = x_aggregated + size;
    G2 *y_tmp = y_aggregated + size;
    for (int i = 0; i < size; i++) // ideally want x to arranged in [round][proof_num], to use mulvec.
    {
        for (int l = 0; l < proof_num; l++)
        {
            x_tmp[l] = x[l][i];
            y_tmp[l] = y[l][i];
        }
        x_aggregated[i] = ip_F_G1(proof->rand_a, x_tmp, proof_num);
        y_aggregated[i] = ip_F_G2(proof->rand_a, y_tmp, proof_num);
    }
    proof->cL_x_coms[round] = ip_G1_G2(x_aggregated + half_size, ck1, half_size); // com(ck1, x[m':])
    proof->cL_y_coms[round] = ip_G1_G2(ck2 + half_size, y_aggregated, half_size); // com(ck2, y[:m'])
    proof->cR_x_coms[round] = ip_G1_G2(x_aggregated, ck1 + half_size, half_size); // com(ck1[m':], x[:m'])
    proof->cR_y_coms[round] = ip_G1_G2(ck2, y_aggregated + half_size, half_size); // com(ck2[:m'], y[m':])

    delete[] x_aggregated;
    delete[] y_aggregated;

    F r_cha = non_zero_rand();
    proof->r_challenges[round] = r_cha;
    for (int i = 0; i < half_size; i++)
    {
        for (int l = 0; l < proof_num; l++)
        {
            x[l][i] = x[l][i] + x[l][i + half_size] * r_cha;
            y[l][i] = y[l][i] + y[l][i + half_size] * (F_ONE / r_cha);
        }
        ck1[i] = ck1[i] + ck1[i + half_size] * (F_ONE / r_cha);
        ck2[i] = ck2[i] + ck2[i + half_size] * r_cha;
    }
}

bool GIPP::verify_proof_batched_tipp(BatchedTIPP_Proof *proof, GT *x_com, GT *y_com, F rlc, int proof_num)
{
    bool ver_res = true;
    int log_size = proof->log_size;
    GT aggregated_z = ip_F_GT(proof->rand_a, proof->z, proof_num);
    G1 aggregated_final_x = ip_F_G1(proof->rand_a, proof->final_x, proof_num);
    G2 aggregated_final_y = ip_F_G2(proof->rand_a, proof->final_y, proof_num);
    GT aggregated_x_com = ip_F_GT(proof->rand_a, x_com, proof_num);
    GT aggregated_y_com = ip_F_GT(proof->rand_a, y_com, proof_num);
    GT cL_x_com_r;
    GT cL_y_com_r;
    GT cR_x_com_rinv;
    GT cR_y_com_rinv;
    GT zL_r;
    GT zR_r;

    F r_cha;
    F *a_r_cha = new F[proof_num];
    F *a_r_cha_inv = new F[proof_num];
    for (int i = 0; i < log_size; i++)
    {
        r_cha = proof->r_challenges[i];
        if (r_cha == F_ZERO)
        {
            cout << "r_cha is zero" << endl;
            return false;
        }
        GT::pow(cL_x_com_r, proof->cL_x_coms[i], r_cha);
        GT::pow(cL_y_com_r, proof->cL_y_coms[i], r_cha);
        GT::pow(cR_x_com_rinv, proof->cR_x_coms[i], F_ONE / r_cha);
        GT::pow(cR_y_com_rinv, proof->cR_y_coms[i], F_ONE / r_cha);
        for (int l = 0; l < proof_num; l++)
        {
            a_r_cha[l] = proof->rand_a[l] * r_cha;
            a_r_cha_inv[l] = proof->rand_a[l] / r_cha;
        }
        zL_r = ip_F_GT(a_r_cha, proof->zLs[i], proof_num);
        zR_r = ip_F_GT(a_r_cha_inv, proof->zRs[i], proof_num);
        aggregated_x_com = cL_x_com_r * cR_x_com_rinv * aggregated_x_com;
        aggregated_y_com = cL_y_com_r * cR_y_com_rinv * aggregated_y_com;
        aggregated_z = zL_r * zR_r * aggregated_z;
    }
    delete[] a_r_cha;
    delete[] a_r_cha_inv;
    GT v_com_x;
    GT v_com_y;
    GT xy;
    millerLoop(v_com_x, aggregated_final_x, proof->final_ck1);
    millerLoop(v_com_y, proof->final_ck2, aggregated_final_y);

    G1 *final_x_a = new G1[proof_num];
    for (int i = 0; i < proof_num; i++)
    {
        final_x_a[i] = proof->final_x[i] * proof->rand_a[i];
    }
    xy = ip_G1_G2(final_x_a, proof->final_y, proof_num);
    delete[] final_x_a;
    if (!pre_exp_GT_equal_check(aggregated_x_com, v_com_x))
    {
        cout << "commitment of final x check fail" << endl;
        ver_res = false;
    }
    if (!pre_exp_GT_equal_check(aggregated_y_com, v_com_y))
    {
        cout << "commitment of final y check fail" << endl;
        ver_res = false;
    }
    if (!pre_exp_GT_equal_check(aggregated_z, xy))
    {
        cout << "commitment of final z check fail" << endl;
        ver_res = false;
    }

    if (log_size == 0)
    {
        if (!(proof->final_ck1 == pk_h2[0] && proof->final_ck2 == pk_g1[0]))
            ver_res = false;
        return ver_res;
    }
    else
    {
        // check e(final_ck2/g^{ck2_val}}, h2) = e(pi_ck2, h^alpha / h^z)
        // check e(g, final_ck1/h^{ck1_val}) = e(g^beta/g^z, pi_ck1)

        G2 ck1_l = proof->final_ck1 - (h2 * proof->ck1_val);
        G1 ck1_r = vk_g_beta - g1 * proof->r_cha_ck1;
        G1 ck2_l = proof->final_ck2 - (g1 * proof->ck2_val);
        G2 ck2_r = vk_h_alpha - h2 * proof->r_cha_ck2;
        if (!pairing_equal_check(g1, ck1_l, ck1_r, proof->proof_ck1))
        {
            std::cout << "final ck1 check fail" << endl;
            ver_res = false;
        }
        else if (!pairing_equal_check(ck2_l, h2, proof->proof_ck2, ck2_r))
        {
            std::cout << "final ck2 check fail" << endl;
            ver_res = false;
        }
    }
    return ver_res;
}

void set_dummy_mipp_proof(MIPP_Proof *proof, int log_size, const G1 &g1r, const G2 &g2r, const GT &gtr, const F &fr)
{
    proof->z = g1r;
    proof->final_x = g1r;
    proof->final_y = fr;
    proof->r_c1 = fr;
    proof->r_c2 = fr;
    proof->cL = new GT[log_size];
    proof->cR = new GT[log_size];
    proof->r_challenges = new F[log_size];
    proof->final_ck1 = g2r;
    proof->final_ck2 = g1r;
    proof->log_size = log_size;
    proof->r_cha_ck1 = fr;
    proof->r_cha_ck2 = fr;
    proof->ck1_val = fr;
    proof->ck2_val = fr;
    proof->proof_ck1 = g2r;
    proof->proof_ck2 = g1r;

    for (int i = 0; i < log_size; i++)
    {
        proof->cL[i] = gtr;
        proof->cR[i] = gtr;
        proof->r_challenges[i] = fr;
    }
}

void set_dummy_mipp_proof_k(MIPP_Proof_k *proof, int log_size, const G1 &g1r, const G2 &g2r, const GT &gtr, const F &fr)
{
    proof->z = g1r;
    proof->final_x = g1r;
    proof->r_c = fr;
    proof->final_ck1 = g2r;
    proof->log_size = log_size;
    proof->r_cha_ck1 = fr;
    proof->ck1_val = fr;
    proof->proof_ck1 = g2r;

    proof->cL = new GT[log_size];
    proof->cR = new GT[log_size];
    proof->r_challenges = new F[log_size];
    for (int i = 0; i < log_size; i++)
    {
        proof->cL[i] = gtr;
        proof->cR[i] = gtr;
        proof->r_challenges[i] = fr;
    }
}

void set_dummy_tipp_proof(TIPP_Proof *proof, int log_size, const G1 &g1r, const G2 &g2r, const GT &gtr, const F &fr)
{
    proof->z = gtr;
    proof->final_x = g1r;
    proof->final_y = g2r;
    proof->final_ck1 = g2r;
    proof->final_ck2 = g1r;
    proof->log_size = log_size;
    proof->r_cha_ck1 = fr;
    proof->ck1_val = fr;
    proof->proof_ck1 = g2r;
    proof->r_cha_ck2 = fr;
    proof->ck2_val = fr;
    proof->proof_ck2 = g1r;
    proof->cL_x_coms = new GT[log_size];
    proof->cR_x_coms = new GT[log_size];
    proof->cL_y_coms = new GT[log_size];
    proof->cR_y_coms = new GT[log_size];
    proof->zLs = new GT[log_size];
    proof->zRs = new GT[log_size];
    proof->r_challenges = new F[log_size];
    for (int i = 0; i < log_size; i++)
    {
        proof->cL_x_coms[i] = gtr;
        proof->cR_x_coms[i] = gtr;
        proof->cL_y_coms[i] = gtr;
        proof->cR_y_coms[i] = gtr;
        proof->zLs[i] = gtr;
        proof->zRs[i] = gtr;
        proof->r_challenges[i] = fr;
    }
}

void set_dummy_ipa_proof(IPA_Proof *proof, int log_size, const G1 &g1r, const G2 &g2r, const GT &gtr, const F &fr)
{
    proof->z = fr;
    proof->final_x = fr;
    proof->final_y = fr;
    proof->final_ck1 = g1r;
    proof->final_ck2 = g1r;
    proof->log_size = log_size;
    proof->r_c2 = fr;
    proof->r_cz = fr;
    proof->r_cha_ck1 = fr;
    proof->ck1_val = fr;
    proof->proof_ck1 = g1r;
    proof->r_cha_ck2 = fr;
    proof->ck2_val = fr;
    proof->proof_ck2 = g1r;
    proof->cL = new G1[log_size];
    proof->cR = new G1[log_size];
    proof->r_challenges = new F[log_size];
    for (int i = 0; i < log_size; i++)
    {
        proof->cL[i] = g1r;
        proof->cR[i] = g1r;
        proof->r_challenges[i] = fr;
    }
}

void set_dummy_batched_ipa_proof(BatchedIPA_Proof *proof, int proof_num, int log_size, const G1 &g1r, const G2 &g2r, const GT &gtr, const F &fr)
{
    proof->proof_num = proof_num;
    proof->rand_a = new F[proof_num];
    proof->z = new F[proof_num];
    proof->final_x = new F[proof_num];
    proof->final_y = new F[proof_num];
    proof->final_ck1 = g1r;
    proof->final_ck2 = g1r;
    proof->log_size = log_size;
    proof->cL = new G1[log_size];
    proof->cR = new G1[log_size];
    proof->r_c2 = fr;
    proof->r_cz = fr;
    proof->r_challenges = new F[log_size];
    proof->r_cha_ck1 = fr;
    proof->ck1_val = fr;
    proof->proof_ck1 = g1r;
    proof->r_cha_ck2 = fr;
    proof->ck2_val = fr;
    proof->proof_ck2 = g1r;
    for (int i = 0; i < log_size; i++)
    {
        proof->cL[i] = g1r;
        proof->cR[i] = g1r;
        proof->r_challenges[i] = fr;
    }
    for (int i = 0; i < proof_num; i++)
    {
        proof->rand_a[i] = fr;
        proof->z[i] = fr;
        proof->final_x[i] = fr;
        proof->final_y[i] = fr;
    }
}

void set_dummy_batched_tipp_proof(BatchedTIPP_Proof *proof, int proof_num, int log_size, const G1 &g1r, const G2 &g2r, const GT &gtr, const F &fr)
{
    proof->proof_num = proof_num;
    proof->rand_a = new F[proof_num];
    proof->z = new GT[proof_num];
    proof->final_x = new G1[proof_num];
    proof->final_y = new G2[proof_num];
    proof->final_ck1 = g2r;
    proof->final_ck2 = g1r;
    proof->log_size = log_size;
    proof->cL_x_coms = new GT[log_size];
    proof->cR_x_coms = new GT[log_size];
    proof->cL_y_coms = new GT[log_size];
    proof->cR_y_coms = new GT[log_size];
    proof->zLs = new GT *[log_size];
    proof->zRs = new GT *[log_size];
    proof->r_challenges = new F[log_size];
    proof->r_cha_ck1 = fr;
    proof->ck1_val = fr;
    proof->proof_ck1 = g2r;
    proof->r_cha_ck2 = fr;
    proof->ck2_val = fr;
    proof->proof_ck2 = g1r;

    for (int i = 0; i < log_size; i++)
    {
        proof->cL_x_coms[i] = gtr;
        proof->cR_x_coms[i] = gtr;
        proof->cL_y_coms[i] = gtr;
        proof->cR_y_coms[i] = gtr;
        proof->r_challenges[i] = fr;
        proof->zLs[i] = new GT[proof_num];
        proof->zRs[i] = new GT[proof_num];
        for (int l = 0; l < proof_num; l++)
        {
            proof->zLs[i][l] = gtr;
            proof->zRs[i][l] = gtr;
        }
    }
    for (int i = 0; i < proof_num; i++)
    {
        proof->rand_a[i] = fr;
        proof->z[i] = gtr;
        proof->final_x[i] = g1r;
        proof->final_y[i] = g2r;
    }
}
