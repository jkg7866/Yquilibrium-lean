// Lean compiler output
// Module: Yquilibrium.Step1
// Imports: public import Init public meta import Init public import Yquilibrium.Calculus public import Yquilibrium.Replica
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
extern lean_object* lp_mathlib_Real_instAddCommMonoid;
lean_object* lp_mathlib_Finset_sum___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Yquilibrium_Yq_Economy_totalU___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Yquilibrium_Yq_Economy_totalU___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Yquilibrium_Yq_Economy_totalU(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Yquilibrium_Yq_Economy_totalU___redArg___lam__0(lean_object* v_x_1_, lean_object* v_u_2_, lean_object* v_i_3_){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; 
lean_inc(v_i_3_);
v___x_4_ = lean_apply_1(v_x_1_, v_i_3_);
v___x_5_ = lean_apply_2(v_u_2_, v_i_3_, v___x_4_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* lp_Yquilibrium_Yq_Economy_totalU___redArg(lean_object* v_inst_6_, lean_object* v_u_7_, lean_object* v_x_8_){
_start:
{
lean_object* v___f_9_; lean_object* v___x_10_; lean_object* v___x_11_; 
v___f_9_ = lean_alloc_closure((void*)(lp_Yquilibrium_Yq_Economy_totalU___redArg___lam__0), 3, 2);
lean_closure_set(v___f_9_, 0, v_x_8_);
lean_closure_set(v___f_9_, 1, v_u_7_);
v___x_10_ = lp_mathlib_Real_instAddCommMonoid;
v___x_11_ = lp_mathlib_Finset_sum___redArg(v___x_10_, v_inst_6_, v___f_9_);
return v___x_11_;
}
}
LEAN_EXPORT lean_object* lp_Yquilibrium_Yq_Economy_totalU(lean_object* v_K_12_, lean_object* v_N_13_, lean_object* v_inst_14_, lean_object* v_u_15_, lean_object* v_x_16_){
_start:
{
lean_object* v___x_17_; 
v___x_17_ = lp_Yquilibrium_Yq_Economy_totalU___redArg(v_inst_14_, v_u_15_, v_x_16_);
return v___x_17_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Yquilibrium_Yquilibrium_Calculus(uint8_t builtin);
lean_object* initialize_Yquilibrium_Yquilibrium_Replica(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Yquilibrium_Yquilibrium_Step1(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
lean_initialize();
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Yquilibrium_Yquilibrium_Calculus(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Yquilibrium_Yquilibrium_Replica(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
