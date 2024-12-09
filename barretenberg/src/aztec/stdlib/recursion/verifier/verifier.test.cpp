#include "verifier.hpp"
#include <gtest/gtest.h>
#include <iostream>

#include <ecc/curves/bn254/fr.hpp>
#include <ecc/curves/bn254/g1.hpp>

#include <plonk/transcript/transcript.hpp>
#include <stdlib/types/turbo.hpp>

#include <ecc/curves/bn254/fq12.hpp>
#include <ecc/curves/bn254/pairing.hpp>

#include "../../hash/pedersen/pedersen.hpp"
#include "../../hash/blake2s/blake2s.hpp"

#include "program_settings.hpp"
#include <stdlib/hash/sha256/sha256.hpp>
#include <plonk/composer/turbo_composer.hpp>
#include <ecc/curves/grumpkin/grumpkin.hpp>
#include <crypto/pedersen/pedersen.hpp>
#include <sys/time.h>
//#include <ctime>
//#include <windows.h>
#include "leveldb/db.h"
#include "../../merkle_tree/leveldb_store.hpp"
#include "../../merkle_tree/leveldb_tx.hpp"
#include "../../merkle_tree/memory_store.hpp"
#include <numeric/random/engine.hpp>

using namespace plonk;
using namespace std;
using namespace plonk::stdlib::types::turbo;
typedef stdlib::byte_array<Composer> byte_array;
typedef stdlib::field_t<waffle::TurboComposer> field_t;
typedef stdlib::witness_t<waffle::TurboComposer> witness_t;
//typedef stdlib::public_witness_t<waffle::TurboComposer> public_witness_t;

struct srs{
	waffle::TurboProver prover_key;
	waffle::TurboVerifier verifier_key;
    waffle::UnrolledTurboProver recursive_key;
    std::shared_ptr<waffle::verification_key> vrfy_key;
    //shared_ptr<waffle::TurboComposer> composer;
	field_t vk;
    int period;
    //waffle::TurboComposer& composer;
};

struct SK{
	field_ct sk;
	field_ct r;
	waffle::plonk_proof proof;
};

struct srs_set{
	struct srs srs_update;
	struct srs srs_init;
    struct srs srs_sign;
    struct srs srs_sign2;
    struct srs srs_agg;
    //struct srs srs_update;
};

struct Sign{
std::vector<unsigned char> sig;
waffle::plonk_proof proof;
int sig_type;
};

long diffclock(struct timeval end,struct timeval start)
{
    long time = 1000*(end.tv_sec - start.tv_sec) + (end.tv_usec - start.tv_usec)/1000;
    //double msec = (double)(time/1000000);
    return time;
}


void create_inner_circuit_keygen(waffle::TurboComposer& composer, std::vector<barretenberg::fr>& public_inputs)
{
    
    field_ct sk(witness_ct(&composer, public_inputs[0]));
   // field_ct r(public_witness_ct(&composer, public_inputs[1]));
    field_ct r(witness_ct(&composer, public_inputs[1]));
    composer.fix_witness(sk.witness_index, sk.get_value());
    composer.fix_witness(r.witness_index, r.get_value());
    
    //cout<<composer.variables.size()<<endl; // 3

    field_t out=stdlib::pedersen::compress(sk,r);
    //cout<<composer.variables.size()<<endl; // 1035
    field_ct hash_out(public_witness_ct(&composer,out.get_value()));
    //cout<<composer.variables.size()<<endl; // 1036
    composer.fix_witness(hash_out.witness_index,hash_out.get_value());
    printf("composer gates = %zu\n", composer.get_num_gates());	
}

void create_inner_circuit_update(waffle::TurboComposer& composer, field_ct sk_prev) //)
{
   // field_ct proof_old(public_witness_ct(&composer, proof));
    field_ct sk_old(witness_ct(&composer, sk_prev.get_value()));
    field_ct tmp(witness_ct(&composer,barretenberg::fr::one()));
    //composer.fix_witness(proof.witness_index,proof.get_value());
    composer.fix_witness(tmp.witness_index,tmp.get_value());
    composer.fix_witness(sk_old.witness_index, sk_old.get_value());

    field_ct sk_update = stdlib::pedersen::compress(sk_old,tmp);
    field_ct sk_new(public_witness_ct(&composer,sk_update.get_value()));
    composer.fix_witness(sk_new.witness_index,sk_new.get_value());
    //composer.fix_witness(proof_old.witness_index, proof_old.get_value());
    printf("composer gates = %zu\n", composer.get_num_gates());
}

void create_inner_circuit_sign(waffle::TurboComposer& composer, field_ct sk_new,vector<uint8_t>concat_data) //)
{
   // field_ct proof_old(public_witness_ct(&composer, proof));
    field_ct sk(witness_ct(&composer, sk_new.get_value()));
    composer.fix_witness(sk.witness_index, sk.get_value());

    byte_array message(&composer,concat_data);
    //byte_array_ct data(public_witness_ct(&composer,stoul(message.get_value(),nullptr,0)));
    //composer.fix_witness(data.witness_index, data.get_value());
    byte_array hash_value = stdlib::pedersen::compress(message);
    //field_ct sig(public_witness_ct(&composer,stoul(hash_value.get_value(),nullptr,0)));
    //composer.fix_witness(sig.witness_index, sig.get_value());
    printf("composer gates = %zu\n", composer.get_num_gates());
}

void create_inner_circuit_agg(waffle::TurboComposer& composer,vector<uint8_t>concat_data) //)
{
    byte_array message(&composer,concat_data);
    std::cout<<"data assign complete"<<std::endl;
    byte_array hash_value = stdlib::pedersen::compress(message);
    printf("composer gates = %zu\n", composer.get_num_gates());
}


// Ok, so we need to create a recursive circuit...
struct circuit_outputs {
    stdlib::recursion::recursion_output<field_ct, group_ct> recursion_output;
    std::shared_ptr<waffle::verification_key> verification_key;
};

struct circuit_outputs_agg {
    stdlib::recursion::recursion_output<field_ct, group_ct> recursion_output1;
    stdlib::recursion::recursion_output<field_ct, group_ct> recursion_output2;
    std::shared_ptr<waffle::verification_key> verification_key1;
    std::shared_ptr<waffle::verification_key> verification_key2;
};
circuit_outputs create_outer_circuit(waffle::TurboComposer& inner_composer, waffle::TurboComposer& outer_composer)
{
    waffle::UnrolledTurboProver prover = inner_composer.create_unrolled_prover();

    std::shared_ptr<waffle::verification_key> verification_key = inner_composer.compute_verification_key();

    waffle::plonk_proof recursive_proof = prover.construct_proof();
    transcript::Manifest recursive_manifest =
        waffle::TurboComposer::create_unrolled_manifest(prover.key->num_public_inputs);

    stdlib::recursion::recursion_output<field_ct, group_ct> output =
        stdlib::recursion::verify_proof<waffle::TurboComposer,
                                        plonk::stdlib::recursion::recursive_turbo_verifier_settings>(
            &outer_composer, verification_key, recursive_manifest, recursive_proof);
    return { output, verification_key};
}

circuit_outputs create_outer_circuit_update(std::shared_ptr<waffle::proving_key> recursion_key,waffle::TurboComposer& outer_composer_update,waffle::plonk_proof recursive_proof,std::shared_ptr<waffle::verification_key> verification_key)
{
    transcript::Manifest recursive_manifest =waffle::TurboComposer::create_unrolled_manifest(recursion_key->num_public_inputs);
    stdlib::recursion::recursion_output<field_ct, group_ct> output =
        stdlib::recursion::verify_proof<waffle::TurboComposer,
                                        plonk::stdlib::recursion::recursive_turbo_verifier_settings>(
            &outer_composer_update, verification_key, recursive_manifest, recursive_proof);
    return { output, verification_key};
}

circuit_outputs create_outer_circuit_aggregate(waffle::TurboComposer& outer_composer_aggregate,std::shared_ptr<waffle::proving_key> recursion_key1,std::shared_ptr<waffle::proving_key> recursion_key2,waffle::plonk_proof recursive_proof1,waffle::plonk_proof recursive_proof2,std::shared_ptr<waffle::verification_key> verification_key1,std::shared_ptr<waffle::verification_key> verification_key2)
{
    transcript::Manifest recursive_manifest1 =waffle::TurboComposer::create_unrolled_manifest(recursion_key1->num_public_inputs);
    transcript::Manifest recursive_manifest2 =waffle::TurboComposer::create_unrolled_manifest(recursion_key2->num_public_inputs);
    /*stdlib::recursion::recursion_output<field_ct, group_ct> output1 =
        stdlib::recursion::verify_proof<waffle::TurboComposer,
                                        plonk::stdlib::recursion::recursive_turbo_verifier_settings>(
            &outer_composer_aggregate, verification_key1, recursive_manifest1, recursive_proof1);*/
    cout<<"aggregate start" <<endl;
    stdlib::recursion::recursion_output<field_ct, group_ct> output =stdlib::recursion::verify_proof_agg<waffle::TurboComposer,
                                        plonk::stdlib::recursion::recursive_turbo_verifier_settings>(
            &outer_composer_aggregate, verification_key1, verification_key2, recursive_manifest1,recursive_manifest2, recursive_proof1,recursive_proof2);

            //byte_array_ct output(witness_ct(&outer_composer_aggregate, recursive_proof1.proof_data));
    

    return { output,verification_key1};
}


void Keygen_composer(std::vector<barretenberg::fr> &inner_inputs,waffle::TurboComposer &outer_composer_keygen, struct circuit_outputs circuit_output,waffle::plonk_proof proof,std::shared_ptr<waffle::proving_key> recursion_key,std::shared_ptr<waffle::verification_key> verification_key){
    circuit_output = create_outer_circuit_update(recursion_key,outer_composer_keygen,proof,verification_key);
    g1::affine_element P[2];
    P[0].x = barretenberg::fq(circuit_output.recursion_output.P0.x.get_value().lo);
    P[0].y = barretenberg::fq(circuit_output.recursion_output.P0.y.get_value().lo);
    P[1].x = barretenberg::fq(circuit_output.recursion_output.P1.x.get_value().lo);
    P[1].y = barretenberg::fq(circuit_output.recursion_output.P1.y.get_value().lo);
    barretenberg::fq12 inner_proof_result = barretenberg::pairing::reduced_ate_pairing_batch_precomputed(P, circuit_output.verification_key->reference_string->get_precomputed_g2_lines(), 2);
    EXPECT_EQ(circuit_output.recursion_output.public_inputs[0].get_value(), crypto::pedersen::compress_native(inner_inputs[0],inner_inputs[1]));
   // EXPECT_EQ(circuit_output.recursion_output.public_inputs[1].get_value(), inner_inputs[1]);
    EXPECT_EQ(inner_proof_result, barretenberg::fq12::one());
}

srs CRS_Keygen(std::vector<barretenberg::fr> &inner_inputs,waffle::TurboComposer &outer_composer_keygen)
{
    struct srs tmp;
    std::cout<<"verification key generation ..." <<std::endl; 
	tmp.vk = crypto::pedersen::compress_native(inner_inputs[0],inner_inputs[1]);
    std::cout<<"verification key end" <<std::endl;
    std::cout<<"crs generation for Keygen start"<<std::endl;
    tmp.prover_key = outer_composer_keygen.create_prover();
    tmp.verifier_key = outer_composer_keygen.create_verifier();
    tmp.recursive_key = outer_composer_keygen.create_unrolled_prover();
    tmp.vrfy_key = outer_composer_keygen.compute_verification_key();
    std::cout << "crs generation for Keygen end" <<std::endl;
    tmp.period = 0;
    return tmp;
}

void Update_composer(struct circuit_outputs circuit_output,waffle::TurboComposer &outer_composer_update,field_ct sk_old,field_ct sk_new,int period,waffle::plonk_proof proof,std::shared_ptr<waffle::proving_key> recursion_key,std::shared_ptr<waffle::verification_key> verification_key){
    //struct circuit_outputs circuit_output;

    circuit_output = create_outer_circuit_update(recursion_key, outer_composer_update,proof,verification_key);
    cout << sizeof(circuit_output.verification_key) <<endl;

    g1::affine_element P[2];
    P[0].x = barretenberg::fq(circuit_output.recursion_output.P0.x.get_value().lo);
    P[0].y = barretenberg::fq(circuit_output.recursion_output.P0.y.get_value().lo);
    P[1].x = barretenberg::fq(circuit_output.recursion_output.P1.x.get_value().lo);
    P[1].y = barretenberg::fq(circuit_output.recursion_output.P1.y.get_value().lo);
    barretenberg::fq12 inner_proof_result = barretenberg::pairing::reduced_ate_pairing_batch_precomputed(P, circuit_output.verification_key->reference_string->get_precomputed_g2_lines(), 2);
    if(period ==0){
    std::cout<<"period : 0" <<std::endl;
    //EXPECT_EQ(circuit_output.recursion_output.public_inputs[0].get_value(), vk.get_value());
    //EXPECT_EQ(circuit_output.recursion_output.public_inputs[0].get_value(), sk_new.get_value());
    }
    else{
    //EXPECT_EQ(circuit_output.recursion_output.public_inputs[0].get_value(), sk_new.get_value());
    EXPECT_EQ(crypto::pedersen::compress_native(sk_old.get_value(),barretenberg::fr::one()),sk_new.get_value());
    }
    EXPECT_EQ(inner_proof_result, barretenberg::fq12::one());
}

void Sign_composer(struct circuit_outputs circuit_output,waffle::TurboComposer &outer_composer_sign,waffle::plonk_proof proof,std::shared_ptr<waffle::proving_key> recursion_key,std::shared_ptr<waffle::verification_key> verification_key){
    //struct circuit_outputs circuit_output;

    circuit_output = create_outer_circuit_update(recursion_key, outer_composer_sign,proof,verification_key);
    
    g1::affine_element P[2];
    P[0].x = barretenberg::fq(circuit_output.recursion_output.P0.x.get_value().lo);
    P[0].y = barretenberg::fq(circuit_output.recursion_output.P0.y.get_value().lo);
    P[1].x = barretenberg::fq(circuit_output.recursion_output.P1.x.get_value().lo);
    P[1].y = barretenberg::fq(circuit_output.recursion_output.P1.y.get_value().lo);
    barretenberg::fq12 inner_proof_result = barretenberg::pairing::reduced_ate_pairing_batch_precomputed(P, circuit_output.verification_key->reference_string->get_precomputed_g2_lines(), 2);

    EXPECT_EQ(inner_proof_result, barretenberg::fq12::one());
}

void Agg_composer(waffle::TurboComposer &outer_composer_agg,std::shared_ptr<waffle::proving_key> recursion_key1,std::shared_ptr<waffle::proving_key> recursion_key2,
waffle::plonk_proof proof1,waffle::plonk_proof proof2,std::shared_ptr<waffle::verification_key> verification_key1,std::shared_ptr<waffle::verification_key> verification_key2){
    //struct circuit_outputs circuit_output;
    auto circuit_output = create_outer_circuit_aggregate(outer_composer_agg,recursion_key1,recursion_key2,proof1,proof2,verification_key1,verification_key2);
    //circuit_output1 = create_outer_circuit_update(recursion_key1,outer_composer_agg,proof1,verification_key1);

    /*g1::affine_element P1[2];
    P1[0].x = barretenberg::fq(circuit_output.recursion_output.P0.x.get_value().lo);
    P1[0].y = barretenberg::fq(circuit_output.recursion_output.P0.y.get_value().lo);
    P1[1].x = barretenberg::fq(circuit_output.recursion_output.P1.x.get_value().lo);
    P1[1].y = barretenberg::fq(circuit_output.recursion_output.P1.y.get_value().lo);
    barretenberg::fq12 inner_proof_result1 = barretenberg::pairing::reduced_ate_pairing_batch_precomputed(P1, circuit_output.verification_key->reference_string->get_precomputed_g2_lines(), 2);
    EXPECT_EQ(inner_proof_result1, barretenberg::fq12::one());*/
    //circuit_output2 = create_outer_circuit_update(recursion_key2,outer_composer_agg,proof2,verification_key2);
    
    /*g1::affine_element P2[2];
    P2[0].x = barretenberg::fq(circuit_output.recursion_output2.P0.x.get_value().lo);
    P2[0].y = barretenberg::fq(circuit_output.recursion_output2.P0.y.get_value().lo);
    P2[1].x = barretenberg::fq(circuit_output.recursion_output2.P1.x.get_value().lo);
    P2[1].y = barretenberg::fq(circuit_output.recursion_output2.P1.y.get_value().lo);
    barretenberg::fq12 inner_proof_result2 = barretenberg::pairing::reduced_ate_pairing_batch_precomputed(P2, circuit_output.verification_key2->reference_string->get_precomputed_g2_lines(), 2);
    
    EXPECT_EQ(inner_proof_result2, barretenberg::fq12::one());
    */
}


srs CRS_Update(waffle::TurboComposer &outer_composer_update,field_t vk, int period)
{	
    struct srs tmp;
    
    tmp.vk = vk;
    tmp.prover_key = outer_composer_update.create_prover();
    tmp.verifier_key = outer_composer_update.create_verifier();
    tmp.recursive_key = outer_composer_update.create_unrolled_prover();
    tmp.vrfy_key = outer_composer_update.compute_verification_key();
    tmp.period = period +1;
    //tmp.composer = outer_composer_update;  
    std::cout<<"update setup end..." <<std::endl;
    return tmp;
}

srs CRS_Sign(waffle::TurboComposer &outer_composer_sign,field_t vk, int period)
{	
    struct srs tmp;   
    tmp.vk = vk;
    tmp.prover_key = outer_composer_sign.create_prover();
    tmp.verifier_key = outer_composer_sign.create_verifier();
    tmp.recursive_key = outer_composer_sign.create_unrolled_prover();
    tmp.vrfy_key = outer_composer_sign.compute_verification_key();
    tmp.period = period;
    //tmp.composer = outer_composer_update;  
    std::cout<<"sign setup end..." <<std::endl;
    return tmp;
}

SK Pri_keygen(){
	struct SK sk_init;
        //generate private key
        std::vector<barretenberg::fr> inner_inputs{ barretenberg::fr::random_element(),barretenberg::fr::random_element()};
        sk_init.sk = inner_inputs[0];
        sk_init.r = inner_inputs[1];
	return sk_init;
}

field_ct Setup_update(struct SK sk_old){
//struct srs srs_upd;
std::cout<<"update start" <<std::endl;
struct SK sk_new;
sk_new.sk = crypto::pedersen::compress_native(sk_old.sk.get_value(),barretenberg::fr::one());
std::cout<<"hashing compledted." <<std::endl;
return sk_new.sk;
}

bool IO_check_update(field_ct sk_old, field_ct sk_new){
    waffle::TurboComposer tmp = waffle::TurboComposer();
    field_ct one(witness_ct(&tmp,barretenberg::fr::one()));
    field_ct sk_tmp(witness_ct(&tmp,sk_old.get_value()));
    field_t sk_new_key=stdlib::pedersen::compress(sk_tmp,one);
    if(sk_new_key.get_value() == sk_new.get_value()){
        std::cout<<"I/O check success!"<<std::endl;
        return true;
    }
    else{
        std::cout<<"I/O check fail!"<<std::endl;
        return false;
    }
}


vector<uint8_t> data_gen(std::string m, int period, field_t vk){
    std::vector<uint64_t> vk_vec;
    std::vector<uint8_t> data;
    uint8_t *ptr = (uint8_t*)&vk_vec;
    for(long unsigned int i=0;i<sizeof(vk.get_value());i++){
        vk_vec.push_back(vk.get_value().data[i]);
        data.push_back(*ptr);
        ptr++;
    }  // insert vk
    data.push_back((uint8_t)period); // insert period
    std::vector<uint8_t> M(m.begin(),m.end());
    for(long unsigned int i=0; i<sizeof(M);i++){
        data.push_back(M[i]);
    }
    return data;  
}

vector<uint8_t> hash_to_data(std::vector<unsigned char> sig1,std::vector<unsigned char> sig2){
    std::vector<uint8_t> data(sig1.begin(),sig1.end());
    uint8_t *ptr = (uint8_t*)&sig2;
    //std::vector<unsigned char> M2(sig2.begin(),sig2.end());
    for(long unsigned int i=0; i<sizeof(sig2);i++){
        data.push_back(*ptr);
        ptr++;
    }
    return data;  
}

void Sig_gen(struct Sign sig,std::vector<unsigned char> data){
    sig.sig = data;
    sig.sig_type = 0;
}

void Agg_gen(struct Sign sig,std::vector<unsigned char> data){
    sig.sig = data;
    sig.sig_type = 1;
}


TEST(stdlib_verifier, test_recursive_proof_composition)
{
    struct srs_set srs_all;
	struct SK sk_init;
    struct SK sk_update; 
    struct circuit_outputs output;
    struct Sign sign;
    struct Sign sign2;
    struct Sign agg_sign;

    struct timeval start;
    struct timeval end;
    //bool result_IO;
    waffle::TurboComposer inner_composer_keygen = waffle::TurboComposer();
    waffle::TurboComposer outer_composer_keygen = waffle::TurboComposer();
    waffle::TurboComposer outer_composer_update = waffle::TurboComposer();
    waffle::TurboComposer outer_composer_update_2 = waffle::TurboComposer();
    waffle::TurboComposer outer_composer_sign = waffle::TurboComposer();
    waffle::TurboComposer outer_composer_sign2 = waffle::TurboComposer();
    waffle::TurboComposer outer_composer_agg = waffle::TurboComposer();
    

    gettimeofday(&start,NULL);
    std::cout<<"Private key generation start"<<std::endl;
	sk_init=Pri_keygen();
    gettimeofday(&end,NULL);
    auto exe_time = diffclock(end,start);
    std::cout<<"Private key generation end" <<std::endl;
    printf("private generation[ms] : %ld\n", exe_time);
    //std::cout<<"private key generation time is : " << exe_time << "ms"<<std::endl;
    std::vector<barretenberg::fr> raw_input{sk_init.sk.get_value(),sk_init.r.get_value()};
    cout<<"sk :"<<sk_init.sk.get_value()<<endl;
    gettimeofday(&start,NULL);
    create_inner_circuit_keygen(inner_composer_keygen, raw_input);
    waffle::UnrolledTurboProver prover_gen = inner_composer_keygen.create_unrolled_prover();
    std::shared_ptr<waffle::verification_key> verification_key_gen = inner_composer_keygen.compute_verification_key();
    waffle::plonk_proof recursive_proof_gen = prover_gen.construct_proof();
    gettimeofday(&end,NULL);
    exe_time = diffclock(end,start);
    printf("private key proof generation[ms] : %ld\n", exe_time);
    cout<<"private key proof size : " << (recursive_proof_gen.proof_data.size())*sizeof(recursive_proof_gen.proof_data[0]) << endl;
    cout<<"private key size is : " << sizeof(sk_init.sk.get_value())<<endl;//*(raw_input.size()) <<endl;
    Keygen_composer(raw_input,outer_composer_keygen,output,recursive_proof_gen,prover_gen.key,verification_key_gen);
    srs_all.srs_init=CRS_Keygen(raw_input,outer_composer_keygen);

    cout<<"vk :"<<srs_all.srs_init.vk.get_value()<<endl;
    cout<<"vk size : " <<sizeof(srs_all.srs_init.vk.get_value())<<endl;

    
    /* Update 1 start*/
    sk_update.sk = Setup_update(sk_init);  // hashing sk
    gettimeofday(&start,NULL);
    Update_composer(output,outer_composer_update,sk_init.sk,sk_update.sk,srs_all.srs_init.period,srs_all.srs_init.recursive_key.construct_proof(),srs_all.srs_init.recursive_key.key,srs_all.srs_init.vrfy_key);
    create_inner_circuit_update(outer_composer_update,sk_init.sk);
    srs_all.srs_update = CRS_Update(outer_composer_update,srs_all.srs_init.vk,srs_all.srs_init.period);
    //cout<<"crs size is " <<sizeof(srs_all.srs_update.recursive_key)<<endl;
    gettimeofday(&end,NULL);
    exe_time = diffclock(end,start);
    printf("update setup[ms] : %ld\n", exe_time);
    cout<<"proving key size is " <<sizeof(srs_all.srs_update.recursive_key.widgets)*(srs_all.srs_update.recursive_key.widgets.size())+sizeof(srs_all.srs_update.recursive_key.key->constraint_selectors)
    *(srs_all.srs_update.recursive_key.key->constraint_selectors.size()+srs_all.srs_update.recursive_key.key->constraint_selector_ffts.size()+srs_all.srs_update.recursive_key.key->permutation_selectors.size()+srs_all.srs_update.recursive_key.key->permutation_selectors_lagrange_base.size()+srs_all.srs_update.recursive_key.key->permutation_selector_ffts.size()+srs_all.srs_update.recursive_key.key->wire_ffts.size())
    +sizeof(srs_all.srs_update.recursive_key.key->small_domain)*3 + sizeof(srs_all.srs_update.recursive_key.key->reference_string) + sizeof(srs_all.srs_update.recursive_key.key->lagrange_1)*(srs_all.srs_update.recursive_key.key->lagrange_1.get_size()+srs_all.srs_update.recursive_key.key->opening_poly.get_size()+srs_all.srs_update.recursive_key.key->shifted_opening_poly.get_size()+srs_all.srs_update.recursive_key.key->linear_poly.get_size()+srs_all.srs_update.recursive_key.key->quotient_mid.get_size()+srs_all.srs_update.recursive_key.key->quotient_large.get_size())<<endl;

    //recursive_prover=outer_composer_update.create_unrolled_prover();
    std::cout<< "period :" << srs_all.srs_update.period << std::endl;
    std::cout<<"update proof generation..." <<std::endl;
    gettimeofday(&start,NULL);
    waffle::plonk_proof proof_update = srs_all.srs_update.recursive_key.construct_proof();
    gettimeofday(&end,NULL);
    exe_time = diffclock(end,start);
    printf("update proof generation[ms] : %ld\n", exe_time); 
    sk_update.proof = proof_update;
    std::cout<<"Update end!"<<std::endl;
    cout<<"private key proof size : " << (proof_update.proof_data.size())*sizeof(proof_update.proof_data[0]) << endl;
    waffle::UnrolledTurboVerifier verifier = outer_composer_update.create_unrolled_verifier();
    gettimeofday(&start,NULL);
    bool result_verify=verifier.verify_proof(proof_update);
    gettimeofday(&end,NULL);
    cout <<"evaluation domain size : " <<sizeof(verifier.key->domain) <<endl;
    cout<<"constraint selector size is : " << sizeof(verifier.key->constraint_selectors)*(verifier.key->constraint_selectors.size())<<endl;
    cout <<"permuation selector size is : " << sizeof(verifier.key->constraint_selectors)*(verifier.key->permutation_selectors.size())<<endl;
    //cout <<"affine element size : " <<sizeof(barretenberg::g2::affine_element)<<endl;
    //cout <<"miller_line size : " << sizeof(barretenberg::pairing::miller_lines) <<endl;
    exe_time = diffclock(end,start);
    printf("update verification[ms] : %ld\n", exe_time); 
    //cout<<result_verify<<"-----------------------------------------------------------"<<endl;
    EXPECT_EQ(result_verify, true);
    /*Update 1 end*/


    /* Update 2 start*/

    sk_init.sk = sk_update.sk;
    sk_update.sk = Setup_update(sk_init);  // hashing sk
    gettimeofday(&start,NULL);
    Update_composer(output,outer_composer_update_2,sk_init.sk,sk_update.sk,srs_all.srs_update.period,proof_update,srs_all.srs_update.recursive_key.key,srs_all.srs_update.vrfy_key);
    create_inner_circuit_update(outer_composer_update_2,sk_init.sk);
    srs_all.srs_update = CRS_Update(outer_composer_update_2,srs_all.srs_init.vk,srs_all.srs_update.period);  
    gettimeofday(&end,NULL);
    exe_time = diffclock(end,start);
    //exe_time = (float)(end-start);
    printf("update  setup[ms] : %ld\n", exe_time); 

    std::cout<< "period :" << srs_all.srs_update.period << std::endl;
    std::cout<<"update proof generation..." <<std::endl;
    gettimeofday(&start,NULL);
    sk_update.proof = srs_all.srs_update.recursive_key.construct_proof();
    gettimeofday(&end,NULL);
    exe_time = diffclock(end,start);
    printf("update proof generation[ms] : %ld\n", exe_time);
    std::cout<<"Update end!"<<std::endl;
    cout<<"private key proof size : " << (sk_update.proof.proof_data.size())*sizeof(sk_update.proof.proof_data[0]) << endl;
    
     
    waffle::UnrolledTurboVerifier verifier_2 = outer_composer_update.create_unrolled_verifier();
    //clock_gettime(CLOCK_REALTIME, &start);
    gettimeofday(&start,NULL);
    result_verify=verifier_2.verify_proof(proof_update);
    gettimeofday(&end,NULL);
    //clock_gettime(CLOCK_REALTIME, &end);
    exe_time = diffclock(end,start);
    printf("update verification time[ms] : %ld\n", exe_time);
    EXPECT_EQ(result_verify, true);
    /*Update 2 end*/


    /*Sign generation*/ 
      std::string message = "TEST";
      vector<uint8_t> Signed_data(data_gen(message,srs_all.srs_update.period,srs_all.srs_update.vk));
      std::vector<unsigned char> data(crypto::pedersen::compress_native(Signed_data));
      
      gettimeofday(&start,NULL);
      Sign_composer(output,outer_composer_sign,sk_update.proof,srs_all.srs_update.recursive_key.key,srs_all.srs_update.vrfy_key);
      create_inner_circuit_sign(outer_composer_sign,sk_update.sk,Signed_data);
      srs_all.srs_sign = CRS_Sign(outer_composer_sign,srs_all.srs_init.vk,srs_all.srs_update.period);
      gettimeofday(&end,NULL);
      exe_time = diffclock(end,start);
      printf("sign setup time[ms] : %ld\n", exe_time);

      std::cout<<"sign proof generation..." <<std::endl;
      gettimeofday(&start,NULL);
      sign.proof = srs_all.srs_sign.recursive_key.construct_proof();
      Sig_gen(sign,data);
      gettimeofday(&end,NULL);
      exe_time = diffclock(end,start);
      printf("sign proof generation time[ms] : %ld\n", exe_time);
      cout<<"proof size is : " << (sign.proof.proof_data.size())*sizeof(sign.proof.proof_data[0]) << endl;
      cout<<"hash output size is  : " << data.size()*sizeof(data) <<endl;
        
      waffle::UnrolledTurboVerifier verifier_sig = outer_composer_sign.create_unrolled_verifier();
      gettimeofday(&start,NULL);
      bool proof_result = verifier_sig.verify_proof(sign.proof);
      gettimeofday(&end,NULL);
      exe_time = diffclock(end,start);
      printf("sign verification generation time[ms] : %ld\n", exe_time);
      EXPECT_EQ(proof_result, true);
      
    /*Sign generation END*/  

        /*Sign generation*/ 

  
      message = "Some";
      vector<uint8_t> Signed_data2(data_gen(message,srs_all.srs_update.period,srs_all.srs_update.vk));
      std::vector<unsigned char> data2(crypto::pedersen::compress_native(Signed_data));
      gettimeofday(&start,NULL);
      Sign_composer(output,outer_composer_sign2,sk_update.proof,srs_all.srs_update.recursive_key.key,srs_all.srs_update.vrfy_key);
      create_inner_circuit_sign(outer_composer_sign2,sk_update.sk,Signed_data);
      srs_all.srs_sign2 = CRS_Sign(outer_composer_sign2,srs_all.srs_init.vk,srs_all.srs_update.period);
      gettimeofday(&end,NULL);
      //exe_time = (double)(end-start);
      exe_time = diffclock(end,start);
      //std::cout<<"signature proof setup time is : " << exe_time << "ms"<<std::endl;
      printf("sign setup time[ms] : %ld\n", exe_time);
      
      std::cout<<"sign proof generation..." <<std::endl;
      gettimeofday(&start,NULL);
      sign2.proof = srs_all.srs_sign2.recursive_key.construct_proof();
      Sig_gen(sign2,data);
      gettimeofday(&end,NULL);
      exe_time = diffclock(end,start);
      printf("sign proof generation time[ms] : %ld\n", exe_time);

      //std::cout<<"proof generation time is : " << exe_time << "ms"<<std::endl;
      waffle::UnrolledTurboVerifier verifier_sig_2 = outer_composer_sign2.create_unrolled_verifier();
      gettimeofday(&start,NULL);
      proof_result = verifier_sig_2.verify_proof(sign2.proof);
      gettimeofday(&end,NULL);
      exe_time = diffclock(end,start);
      printf("sign verification generation time[ms] : %ld\n", exe_time);
      //std::cout<<"verification time is : " << exe_time << "ms"<<std::endl;
      EXPECT_EQ(proof_result, true);
    /*Sign generation END*/  
    
    
    /*aggregation start*/
    gettimeofday(&start,NULL);
    std::vector<uint8_t>agg_data(hash_to_data(sign.sig,sign2.sig));
    Agg_composer(outer_composer_agg,srs_all.srs_sign.recursive_key.key,srs_all.srs_sign2.recursive_key.key,sign.proof,sign2.proof,srs_all.srs_sign.vrfy_key,srs_all.srs_sign2.vrfy_key);
    create_inner_circuit_agg(outer_composer_agg,agg_data);
    srs_all.srs_agg = CRS_Sign(outer_composer_agg,srs_all.srs_init.vk,srs_all.srs_update.period);
    gettimeofday(&end,NULL);
    //exe_time = (float)(end-start);
    exe_time=diffclock(end,start);
    printf("aggregation setup time[ms] : %ld\n", exe_time);
    std::vector<unsigned char> agg(crypto::pedersen::compress_native(agg_data));

        cout<<"proving key size is " <<sizeof(srs_all.srs_agg.recursive_key.widgets)*(srs_all.srs_agg.recursive_key.widgets.size())+sizeof(srs_all.srs_agg.recursive_key.key->constraint_selectors)
    *(srs_all.srs_agg.recursive_key.key->constraint_selectors.size()+srs_all.srs_agg.recursive_key.key->constraint_selector_ffts.size()+srs_all.srs_agg.recursive_key.key->permutation_selectors.size()+srs_all.srs_agg.recursive_key.key->permutation_selectors_lagrange_base.size()+srs_all.srs_agg.recursive_key.key->permutation_selector_ffts.size()+srs_all.srs_agg.recursive_key.key->wire_ffts.size())
    +sizeof(srs_all.srs_agg.recursive_key.key->small_domain)*3 + sizeof(srs_all.srs_agg.recursive_key.key->reference_string) + sizeof(srs_all.srs_agg.recursive_key.key->lagrange_1)*(srs_all.srs_agg.recursive_key.key->lagrange_1.get_size()+srs_all.srs_agg.recursive_key.key->opening_poly.get_size()+srs_all.srs_agg.recursive_key.key->shifted_opening_poly.get_size()+srs_all.srs_agg.recursive_key.key->linear_poly.get_size()+srs_all.srs_agg.recursive_key.key->quotient_mid.get_size()+srs_all.srs_agg.recursive_key.key->quotient_large.get_size())<<endl;
      std::cout<<"aggregation proof generation..." <<std::endl;
      gettimeofday(&start,NULL);
      agg_sign.proof = srs_all.srs_agg.prover_key.construct_proof();
      Agg_gen(agg_sign,agg_data);
      gettimeofday(&end,NULL);
      cout<<"proof size is : " << (agg_sign.proof.proof_data.size())*sizeof(agg_sign.proof.proof_data[0]) << endl;
      exe_time = diffclock(end,start);
      printf("aggregation time[ms] : %ld\n", exe_time);
    
    //waffle::UnrolledTurboVerifier verifier_agg = outer_composer_agg.create_unrolled_verifier();
    //bool proof_result=verifier_agg.verify_proof(agg_sign.proof);
    //bool proof_result = srs_all.srs_agg.verifier_key.verify_proof(agg_sign.proof);
    //EXPECT_EQ(proof_result, true);


    /*group sig start*/


      
}
