#pragma once

#include "../../primitives/field/field.hpp"
#include "../../primitives/bool/bool.hpp"
#include "../../primitives/bigfield/bigfield.hpp"
#include "../../primitives/biggroup/biggroup.hpp"

#include "../transcript/transcript.hpp"

#include <plonk/proof_system/utils/linearizer.hpp>
#include <plonk/proof_system/public_inputs/public_inputs.hpp>

#include <plonk/proof_system/widgets/turbo_fixed_base_widget.hpp>

#include <polynomials/polynomial_arithmetic.hpp>

#include <ecc/curves/bn254/fq12.hpp>
#include <ecc/curves/bn254/pairing.hpp>
#include<vector>
//#include <stdlib/hash/sha256/sha256.hpp>
namespace plonk {
namespace stdlib {
namespace recursion {

template <typename Field, typename Group> struct recursion_output {
    Group P0;
    Group P1;
    // the public inputs of the inner ciruit are now private inputs of the outer circuit!
    std::vector<Field> public_inputs;
};

template <typename Composer> struct lagrange_evaluations {
    field_t<Composer> l_1;
    field_t<Composer> l_n_minus_1;
    field_t<Composer> vanishing_poly;
};

template <typename Composer>
lagrange_evaluations<Composer> get_lagrange_evaluations(const field_t<Composer>& z, const evaluation_domain& domain)
{
    using field_pt = field_t<Composer>;
    field_pt z_pow = z;
    for (size_t i = 0; i < domain.log2_size; ++i) {
        z_pow *= z_pow;
    }
    field_pt numerator = z_pow - field_pt(1);

    lagrange_evaluations<Composer> result;
    result.vanishing_poly = numerator / (z - domain.root_inverse);
    numerator *= domain.domain_inverse;
    result.l_1 = numerator / (z - field_pt(1));
    result.l_n_minus_1 = numerator / ((z * domain.root.sqr()) - field_pt(1));

    barretenberg::polynomial_arithmetic::get_lagrange_evaluations(z.get_value(), domain);
    return result;
}

template <typename Composer, typename program_settings>
recursion_output<
    field_t<Composer>,
    element<Composer, bigfield<Composer, barretenberg::Bn254FqParams>, field_t<Composer>, barretenberg::g1>>
verify_proof(Composer* context,
             std::shared_ptr<waffle::verification_key> key,
             const transcript::Manifest& manifest,
             const waffle::plonk_proof& proof)
{
    using field_pt = field_t<Composer>;
    using fq_pt = bigfield<Composer, barretenberg::Bn254FqParams>;
    using group_pt = element<Composer, fq_pt, field_pt, barretenberg::g1>;

    key->program_width = program_settings::program_width;
    //std::cout<<program_settings::program_width<<std::endl;
    Transcript<Composer> transcript = Transcript<Composer>(context, proof.proof_data, manifest);
    std::array<group_pt, program_settings::program_width> T; // size = 4, element size = 1600
    std::array<group_pt, program_settings::program_width> W; // 4

    std::array<field_pt, program_settings::program_width> wire_evaluations;

    for (size_t i = 0; i < program_settings::program_width; ++i) {
        std::string index = std::to_string(i + 1);
        T[i] = transcript.get_circuit_group_element("T_" + index);
        W[i] = transcript.get_circuit_group_element("W_" + index);
        wire_evaluations[i] = transcript.get_field_element("w_" + index);
    }

    group_pt Z_1 = transcript.get_circuit_group_element("Z");
    group_pt PI_Z = transcript.get_circuit_group_element("PI_Z");
    group_pt PI_Z_OMEGA = transcript.get_circuit_group_element("PI_Z_OMEGA");

    T[0].validate_on_curve();
    Z_1.validate_on_curve();
    PI_Z.validate_on_curve();

    field_t circuit_size(stdlib::witness_t(context, barretenberg::fr(key->n)));
    field_t public_input_size(stdlib::witness_t(context, barretenberg::fr(key->num_public_inputs)));

    transcript.add_field_element("circuit_size", circuit_size);
    transcript.add_field_element("public_input_size", public_input_size);

    transcript.apply_fiat_shamir("init");
    transcript.apply_fiat_shamir("beta");
    transcript.apply_fiat_shamir("alpha");
    transcript.apply_fiat_shamir("z");
    field_pt alpha = transcript.get_challenge_field_element("alpha");
    field_pt z_challenge = transcript.get_challenge_field_element("z");
    lagrange_evaluations<Composer> lagrange_evals = get_lagrange_evaluations(z_challenge, key->domain);

    // reconstruct evaluation of quotient polynomial from prover messages
    field_pt T0;

    field_pt t_eval = field_pt(0);

    field_pt alpha_base = alpha;

    alpha_base = program_settings::compute_quotient_evaluation_contribution(key.get(), alpha_base, transcript, t_eval); // 

    t_eval = t_eval / lagrange_evals.vanishing_poly;
    transcript.add_field_element("t", t_eval);

    transcript.apply_fiat_shamir("nu");
    transcript.apply_fiat_shamir("separator");

    field_pt u = transcript.get_challenge_field_element("separator");

    field_pt batch_evaluation = t_eval;

    for (size_t i = 0; i < program_settings::program_width; ++i) {
        const std::string wire_key = "w_" + std::to_string(i + 1);
        field_pt wire_challenge = transcript.get_challenge_field_element_from_map("nu", wire_key);
        T0 = wire_challenge * wire_evaluations[i];
        batch_evaluation += T0;

        if (program_settings::requires_shifted_wire(program_settings::wire_shift_settings, i)) {
            field_pt wire_shifted_eval = transcript.get_field_element("w_" + std::to_string(i + 1) + "_omega");
            T0 = wire_shifted_eval * wire_challenge;
            T0 *= u;
            batch_evaluation += T0;
        }
    }

    program_settings::compute_batch_evaluation_contribution(key.get(), batch_evaluation, transcript);

    batch_evaluation = -batch_evaluation;

    field_pt z_omega_scalar;
    z_omega_scalar = z_challenge * key->domain.root;
    z_omega_scalar *= u;

    std::vector<field_pt> big_scalars;
    std::vector<group_pt> big_elements;
    std::vector<field_pt> small_scalars;
    std::vector<group_pt> small_elements;

    for (size_t i = 0; i < program_settings::program_width; ++i) {
        W[i].validate_on_curve();
        big_elements.emplace_back(W[i]);

        const std::string wire_key = "w_" + std::to_string(i + 1);
        field_pt wire_challenge = transcript.get_challenge_field_element_from_map("nu", wire_key);

        if (program_settings::requires_shifted_wire(program_settings::wire_shift_settings, i)) {
            T0 = wire_challenge * u;
            T0 += wire_challenge;
            big_scalars.emplace_back(T0);
        } else {
            big_scalars.emplace_back(wire_challenge);
        }
    }

    big_elements.emplace_back(group_pt::one(context));
    big_scalars.emplace_back(batch_evaluation);

    PI_Z_OMEGA.validate_on_curve();
    big_elements.emplace_back(PI_Z_OMEGA);
    big_scalars.emplace_back(z_omega_scalar);

    small_elements.emplace_back(PI_Z);
    small_scalars.emplace_back(z_challenge);

    // TODO FIX
    field_pt z_pow_n = z_challenge; 
    const size_t log2_n = numeric::get_msb(key->n);
    for (size_t j = 0; j < log2_n; ++j) {
        z_pow_n = z_pow_n.sqr();
    }
    field_pt z_power = z_pow_n;
    for (size_t i = 1; i < program_settings::program_width; ++i) {
        T[i].validate_on_curve();
        big_elements.emplace_back(T[i]);
        big_scalars.emplace_back(z_power);

        z_power *= z_pow_n;
    }

    std::vector<barretenberg::g1::affine_element> g1_inputs;
    program_settings::append_scalar_multiplication_inputs(key.get(), alpha, transcript, g1_inputs, small_scalars);
    for (size_t i = 0; i < g1_inputs.size(); ++i) {
        small_elements.push_back(Transcript<waffle::TurboComposer>::convert_g1(context, g1_inputs[i]));
        // TODO: add method of enabling widgets to directly add transcript G1 elements into array
        if (i == 0) {
            auto input = small_elements[small_elements.size() - 1];
            context->assert_equal(Z_1.x.binary_basis_limbs[0].element.witness_index,
                                  input.x.binary_basis_limbs[0].element.witness_index);
            context->assert_equal(Z_1.x.binary_basis_limbs[1].element.witness_index,
                                  input.x.binary_basis_limbs[1].element.witness_index);
            context->assert_equal(Z_1.x.binary_basis_limbs[2].element.witness_index,
                                  input.x.binary_basis_limbs[2].element.witness_index);
            context->assert_equal(Z_1.x.binary_basis_limbs[3].element.witness_index,
                                  input.x.binary_basis_limbs[3].element.witness_index);
            context->assert_equal(Z_1.y.binary_basis_limbs[0].element.witness_index,
                                  input.y.binary_basis_limbs[0].element.witness_index);
            context->assert_equal(Z_1.y.binary_basis_limbs[1].element.witness_index,
                                  input.y.binary_basis_limbs[1].element.witness_index);
            context->assert_equal(Z_1.y.binary_basis_limbs[2].element.witness_index,
                                  input.y.binary_basis_limbs[2].element.witness_index);
            context->assert_equal(Z_1.y.binary_basis_limbs[3].element.witness_index,
                                  input.y.binary_basis_limbs[3].element.witness_index);
            context->assert_equal(Z_1.x.prime_basis_limb.witness_index, input.x.prime_basis_limb.witness_index);
            context->assert_equal(Z_1.y.prime_basis_limb.witness_index, input.y.prime_basis_limb.witness_index);
        }
    }
    group_pt rhs = group_pt::mixed_batch_mul(big_elements, big_scalars, small_elements, small_scalars, 129);
    rhs = (rhs + T[0]).normalize();
    group_pt lhs = group_pt::batch_mul({ PI_Z_OMEGA }, { u }, 128);
    lhs = lhs + PI_Z;
    lhs = (-lhs).normalize();
    return recursion_output<field_pt, group_pt>{
        rhs,
        lhs,
        transcript.get_field_element_vector("public_inputs")
    };
}


template <typename Composer, typename program_settings>
recursion_output<
    field_t<Composer>,
    element<Composer, bigfield<Composer, barretenberg::Bn254FqParams>, field_t<Composer>, barretenberg::g1>>
verify_proof_agg(Composer* context,
             std::shared_ptr<waffle::verification_key> key,std::shared_ptr<waffle::verification_key> key2,
             const transcript::Manifest& manifest,const transcript::Manifest& manifest2,
             const waffle::plonk_proof& proof,const waffle::plonk_proof& proof2)
{
    using field_pt = field_t<Composer>;
    using fq_pt = bigfield<Composer, barretenberg::Bn254FqParams>;
    using group_pt = element<Composer, fq_pt, field_pt, barretenberg::g1>;

    key->program_width = program_settings::program_width;
    
    Transcript<Composer> transcript = Transcript<Composer>(context, proof.proof_data,manifest);
    Transcript<Composer> transcript2 = Transcript<Composer>(context, proof2.proof_data,manifest2);
    std::array<group_pt, program_settings::program_width*2> T;
    std::array<group_pt, program_settings::program_width*2> W;
    std::array<field_pt, program_settings::program_width*2> wire_evaluations;
    std::cout<<"phase 0"<<std::endl;
    std::cout<<program_settings::program_width<<std::endl;
    for (size_t i = 0; i < program_settings::program_width; ++i) {
        std::string index = std::to_string(i + 1);

        T[i] = transcript.get_circuit_group_element("T_" + index);
        W[i] = transcript.get_circuit_group_element("W_" + index);
        wire_evaluations[i] = transcript.get_field_element("w_" + index);
        
        T[i+program_settings::program_width] = transcript2.get_circuit_group_element("T_" + index);
        W[i+program_settings::program_width] = transcript2.get_circuit_group_element("W_" + index);
        wire_evaluations[i+program_settings::program_width] = transcript2.get_field_element("w_" + index);
        
        std::cout<<"assign "<<i<<" completed"<<std::endl;
    }

    std::cout<<"phase 1"<<std::endl;

    group_pt Z_1 = transcript.get_circuit_group_element("Z");
    group_pt PI_Z = transcript.get_circuit_group_element("PI_Z");
    group_pt PI_Z_OMEGA = transcript.get_circuit_group_element("PI_Z_OMEGA");

    group_pt Z_1_2 = transcript2.get_circuit_group_element("Z");
    group_pt PI_Z_2 = transcript2.get_circuit_group_element("PI_Z");
    group_pt PI_Z_OMEGA_2 = transcript2.get_circuit_group_element("PI_Z_OMEGA");

    T[0].validate_on_curve();
    Z_1.validate_on_curve();
    PI_Z.validate_on_curve();

    Z_1_2.validate_on_curve();
    PI_Z_2.validate_on_curve();
    std::cout<<"phase 2"<<std::endl;

    field_t circuit_size(stdlib::witness_t(context, barretenberg::fr((key->n)+(key2->n))));
    std::cout<<"phase 2.5 : circuit assign"<<std::endl;
    field_t public_input_size(stdlib::witness_t(context, barretenberg::fr((key->num_public_inputs)+(key2->num_public_inputs))));
    std::cout<<"phase 2.5 : input assign"<<std::endl;
    //field_t circuit_size2(stdlib::witness_t(context, barretenberg::fr(key2->n)));
    //field_t public_input_size2(stdlib::witness_t(context, barretenberg::fr(key2->num_public_inputs)));
    
    
    transcript.add_field_element("circuit_size", circuit_size);
    transcript.add_field_element("public_input_size", public_input_size);

    transcript.apply_fiat_shamir("init");
    transcript.apply_fiat_shamir("beta");
    transcript.apply_fiat_shamir("alpha");
    transcript.apply_fiat_shamir("z");
    field_pt alpha = transcript.get_challenge_field_element("alpha");
    field_pt z_challenge = transcript.get_challenge_field_element("z");
    lagrange_evaluations<Composer> lagrange_evals = get_lagrange_evaluations(z_challenge, key->domain);


    transcript2.add_field_element("circuit_size", circuit_size);
    transcript2.add_field_element("public_input_size", public_input_size);

    transcript2.apply_fiat_shamir("init");
    transcript2.apply_fiat_shamir("beta");
    transcript2.apply_fiat_shamir("alpha");
    transcript2.apply_fiat_shamir("z");
    field_pt alpha_2 = transcript2.get_challenge_field_element("alpha");
    field_pt z_challenge_2 = transcript2.get_challenge_field_element("z");
    lagrange_evaluations<Composer> lagrange_evals_2 = get_lagrange_evaluations(z_challenge_2, key2->domain);
    std::cout<<"phase 3 : fiat shamir"<<std::endl;

    // reconstruct evaluation of quotient polynomial from prover messages
    field_pt T0;

    field_pt t_eval = field_pt(0);
    field_pt t_eval_2 = field_pt(0);

    field_pt alpha_base = alpha;
    field_pt alpha_base2 = alpha_2;
    
    alpha_base = program_settings::compute_quotient_evaluation_contribution(key.get(), alpha_base, transcript, t_eval);
    alpha_base2 = program_settings::compute_quotient_evaluation_contribution(key2.get(), alpha_base2, transcript2, t_eval);

    std::cout<<"phase 4 : compute_quotient_evaluation_contribution"<<std::endl;
    t_eval = t_eval / lagrange_evals.vanishing_poly;
    t_eval_2 = t_eval_2 / lagrange_evals_2.vanishing_poly;
    transcript.add_field_element("t", t_eval);
    transcript.apply_fiat_shamir("nu");
    transcript.apply_fiat_shamir("separator");

    transcript2.add_field_element("t", t_eval_2);
    transcript2.apply_fiat_shamir("nu");
    transcript2.apply_fiat_shamir("separator");

    field_pt u = transcript.get_challenge_field_element("separator");
    field_pt u2 = transcript2.get_challenge_field_element("separator");
    
    field_pt batch_evaluation = t_eval;
    field_pt batch_evaluation_2 = t_eval_2;
    field_pt wire_challenge;
    field_pt wire_challenge_2;
    std::cout<<"phase 5 : fiat shamir 2"<<std::endl;
    for (size_t i = 0; i < program_settings::program_width*2; ++i) {
        if(i<program_settings::program_width){
        const std::string wire_key = "w_" + std::to_string(i + 1);
        wire_challenge = transcript.get_challenge_field_element_from_map("nu", wire_key);
        if (program_settings::requires_shifted_wire(program_settings::wire_shift_settings, i)) {
            field_pt wire_shifted_eval = transcript.get_field_element("w_" + std::to_string(i + 1) + "_omega");
            T0 = wire_shifted_eval * wire_challenge;
            T0 *= u;
            batch_evaluation += T0;
        }
        T0 = wire_challenge * wire_evaluations[i];
        batch_evaluation += T0;
        }
        else{
        const std::string wire_key = "w_" + std::to_string(i + 1-program_settings::program_width);
        wire_challenge_2 = transcript2.get_challenge_field_element_from_map("nu", wire_key);
        std::cout<<"wire challenge_2" <<std::endl;
        if (program_settings::requires_shifted_wire(program_settings::wire_shift_settings, i)) {
            field_pt wire_shifted_eval = transcript2.get_field_element("w_" + std::to_string(i + 1-program_settings::program_width) + "_omega");
            T0 = wire_shifted_eval * wire_challenge_2;
            T0 *= u2;
            batch_evaluation_2 += T0;
        }
        T0 = wire_challenge * wire_evaluations[i];
        batch_evaluation_2 += T0;
        }
    }
    std::cout<<"phase 5 : wire assign"<<std::endl;
    program_settings::compute_batch_evaluation_contribution(key.get(), batch_evaluation, transcript);
    program_settings::compute_batch_evaluation_contribution(key2.get(), batch_evaluation_2, transcript2);
    
    batch_evaluation = -batch_evaluation;
    batch_evaluation_2 = -batch_evaluation_2;

    field_pt z_omega_scalar;
    z_omega_scalar = z_challenge * key->domain.root;
    z_omega_scalar *= u;

    field_pt z_omega_scalar_2;
    z_omega_scalar_2 = z_challenge_2 * key2->domain.root;
    z_omega_scalar_2 *= u2;

    std::vector<field_pt> big_scalars;
    std::vector<group_pt> big_elements;
    std::vector<field_pt> small_scalars;
    std::vector<group_pt> small_elements;

    for (size_t i = 0; i < program_settings::program_width*2; ++i) {
        W[i].validate_on_curve();
        big_elements.emplace_back(W[i]);

        const std::string wire_key = "w_" + std::to_string(i + 1);
        if(i < program_settings::program_width){
        field_pt wire_challenge = transcript.get_challenge_field_element_from_map("nu", wire_key);
        if (program_settings::requires_shifted_wire(program_settings::wire_shift_settings, i)) {
            T0 = wire_challenge * u;
            T0 += wire_challenge;
            big_scalars.emplace_back(T0);
        } else {
            big_scalars.emplace_back(wire_challenge);
        }
        }
        else{
        const std::string wire_key = "w_" + std::to_string(i + 1-program_settings::program_width);
        field_pt wire_challenge2 = transcript2.get_challenge_field_element_from_map("nu", wire_key);
        if (program_settings::requires_shifted_wire(program_settings::wire_shift_settings, i)) {
            T0 = wire_challenge2 * u2;
            T0 += wire_challenge2;
            big_scalars.emplace_back(T0);
        } else {
            big_scalars.emplace_back(wire_challenge2);
        }
        }
    }

    big_elements.emplace_back(group_pt::one(context));
    big_scalars.emplace_back(batch_evaluation);
    big_scalars.emplace_back(batch_evaluation_2);

    PI_Z_OMEGA.validate_on_curve();
    PI_Z_OMEGA_2.validate_on_curve();
    big_elements.emplace_back(PI_Z_OMEGA);
    big_elements.emplace_back(PI_Z_OMEGA_2);
    big_scalars.emplace_back(z_omega_scalar);
    big_scalars.emplace_back(z_omega_scalar_2);

    small_elements.emplace_back(PI_Z);
    small_elements.emplace_back(PI_Z_2);
    small_scalars.emplace_back(z_challenge);
    small_scalars.emplace_back(z_challenge_2);
    // TODO FIX
    field_pt z_pow_n = z_challenge;
    field_pt z_pow_n2 = z_challenge_2;  
    const size_t log2_n = numeric::get_msb(key->n);
    const size_t log2_n2 = numeric::get_msb(key2->n);
    for (size_t j = 0; j < log2_n; ++j) {
        z_pow_n = z_pow_n.sqr();
    }
    for (size_t k = 0; k < log2_n2; ++k) {
        z_pow_n2 = z_pow_n2.sqr();
    }

    field_pt z_power = z_pow_n;
    field_pt z_power_2 = z_pow_n2;
    for (size_t i = 1; i < program_settings::program_width*2; ++i) {
        T[i].validate_on_curve();
        big_elements.emplace_back(T[i]);
        if(i<program_settings::program_width){
        big_scalars.emplace_back(z_power);
        z_power *= z_pow_n;
        }
        else{
        big_scalars.emplace_back(z_power_2);
        z_power_2 *= z_pow_n2;    
        }
    }

    std::vector<barretenberg::g1::affine_element> g1_inputs;
    std::vector<barretenberg::g1::affine_element> g1_inputs_2;
    program_settings::append_scalar_multiplication_inputs(key.get(), alpha, transcript, g1_inputs, small_scalars);
    program_settings::append_scalar_multiplication_inputs(key2.get(), alpha_2, transcript2, g1_inputs_2, small_scalars);
    //g1_inputs.insert(g1_inputs.end(),g1_inputs_2.begin(),g1_inputs_2.end());
    for (size_t i = 0; i < g1_inputs.size(); ++i) {
        small_elements.push_back(Transcript<waffle::TurboComposer>::convert_g1(context, g1_inputs[i]));
        // TODO: add method of enabling widgets to directly add transcript G1 elements into array
        if (i == 0) {
            auto input = small_elements[small_elements.size() - 1];
            context->assert_equal(Z_1.x.binary_basis_limbs[0].element.witness_index,
                                  input.x.binary_basis_limbs[0].element.witness_index);
            context->assert_equal(Z_1.x.binary_basis_limbs[1].element.witness_index,
                                  input.x.binary_basis_limbs[1].element.witness_index);
            context->assert_equal(Z_1.x.binary_basis_limbs[2].element.witness_index,
                                  input.x.binary_basis_limbs[2].element.witness_index);
            context->assert_equal(Z_1.x.binary_basis_limbs[3].element.witness_index,
                                  input.x.binary_basis_limbs[3].element.witness_index);
            context->assert_equal(Z_1.y.binary_basis_limbs[0].element.witness_index,
                                  input.y.binary_basis_limbs[0].element.witness_index);
            context->assert_equal(Z_1.y.binary_basis_limbs[1].element.witness_index,
                                  input.y.binary_basis_limbs[1].element.witness_index);
            context->assert_equal(Z_1.y.binary_basis_limbs[2].element.witness_index,
                                  input.y.binary_basis_limbs[2].element.witness_index);
            context->assert_equal(Z_1.y.binary_basis_limbs[3].element.witness_index,
                                  input.y.binary_basis_limbs[3].element.witness_index);
            context->assert_equal(Z_1.x.prime_basis_limb.witness_index, input.x.prime_basis_limb.witness_index);
            context->assert_equal(Z_1.y.prime_basis_limb.witness_index, input.y.prime_basis_limb.witness_index);
        }
    }
        for (size_t i = 0; i < g1_inputs_2.size(); ++i) {
        small_elements.push_back(Transcript<waffle::TurboComposer>::convert_g1(context, g1_inputs_2[i]));
        // TODO: add method of enabling widgets to directly add transcript G1 elements into array
        if (i == 0) {
            auto input = small_elements[small_elements.size() - 1];
            context->assert_equal(Z_1_2.x.binary_basis_limbs[0].element.witness_index,
                                  input.x.binary_basis_limbs[0].element.witness_index);
            context->assert_equal(Z_1_2.x.binary_basis_limbs[1].element.witness_index,
                                  input.x.binary_basis_limbs[1].element.witness_index);
            context->assert_equal(Z_1_2.x.binary_basis_limbs[2].element.witness_index,
                                  input.x.binary_basis_limbs[2].element.witness_index);
            context->assert_equal(Z_1_2.x.binary_basis_limbs[3].element.witness_index,
                                  input.x.binary_basis_limbs[3].element.witness_index);
            context->assert_equal(Z_1_2.y.binary_basis_limbs[0].element.witness_index,
                                  input.y.binary_basis_limbs[0].element.witness_index);
            context->assert_equal(Z_1_2.y.binary_basis_limbs[1].element.witness_index,
                                  input.y.binary_basis_limbs[1].element.witness_index);
            context->assert_equal(Z_1_2.y.binary_basis_limbs[2].element.witness_index,
                                  input.y.binary_basis_limbs[2].element.witness_index);
            context->assert_equal(Z_1_2.y.binary_basis_limbs[3].element.witness_index,
                                  input.y.binary_basis_limbs[3].element.witness_index);
            context->assert_equal(Z_1_2.x.prime_basis_limb.witness_index, input.x.prime_basis_limb.witness_index);
            context->assert_equal(Z_1_2.y.prime_basis_limb.witness_index, input.y.prime_basis_limb.witness_index);
            std::cout<<"check"<<std::endl;
        }
    }
    std::cout<<"mix_batch_mul"<<std::endl;
    group_pt rhs = group_pt::mixed_batch_mul(big_elements, big_scalars, small_elements, small_scalars, 129);
    
    rhs = (rhs + T[0]).normalize();
    std::cout<<"normalize"<<std::endl;
    group_pt lhs = group_pt::batch_mul({ PI_Z_OMEGA }, { u }, 128);
    lhs = lhs + PI_Z;
    lhs = (-lhs).normalize();
    return recursion_output<field_pt, group_pt>{
        rhs,
        lhs,
        transcript.get_field_element_vector("public_inputs")
    };
}




} // namespace recursion
} // namespace stdlib
} // namespace plonk
