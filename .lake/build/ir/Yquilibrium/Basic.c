// Lean compiler output
// Module: Yquilibrium.Basic
// Imports: public import Init public meta import Init public import Yquilibrium.Imports
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
lean_object* lp_mathlib___private_Mathlib_Basic_Real_Basic_0__Real_mul___lam__0(lean_object*, lean_object*, lean_object*);
extern lean_object* lp_mathlib_Real_instAddCommMonoid;
lean_object* lp_mathlib_Finset_sum___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Yquilibrium_Yq_dot___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Yquilibrium_Yq_dot___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Yquilibrium_Yq_dot(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Yquilibrium_Yq_dot___redArg___lam__0(lean_object* v_p_1_, lean_object* v_z_2_, lean_object* v_k_3_){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___f_6_; 
lean_inc(v_k_3_);
v___x_4_ = lean_apply_1(v_p_1_, v_k_3_);
v___x_5_ = lean_apply_1(v_z_2_, v_k_3_);
v___f_6_ = lean_alloc_closure((void*)(lp_mathlib___private_Mathlib_Basic_Real_Basic_0__Real_mul___lam__0), 3, 2);
lean_closure_set(v___f_6_, 0, v___x_4_);
lean_closure_set(v___f_6_, 1, v___x_5_);
return v___f_6_;
}
}
LEAN_EXPORT lean_object* lp_Yquilibrium_Yq_dot___redArg(lean_object* v_inst_7_, lean_object* v_p_8_, lean_object* v_z_9_){
_start:
{
lean_object* v___f_10_; lean_object* v___x_11_; lean_object* v___x_12_; 
v___f_10_ = lean_alloc_closure((void*)(lp_Yquilibrium_Yq_dot___redArg___lam__0), 3, 2);
lean_closure_set(v___f_10_, 0, v_p_8_);
lean_closure_set(v___f_10_, 1, v_z_9_);
v___x_11_ = lp_mathlib_Real_instAddCommMonoid;
v___x_12_ = lp_mathlib_Finset_sum___redArg(v___x_11_, v_inst_7_, v___f_10_);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* lp_Yquilibrium_Yq_dot(lean_object* v_K_13_, lean_object* v_inst_14_, lean_object* v_p_15_, lean_object* v_z_16_){
_start:
{
lean_object* v___x_17_; 
v___x_17_ = lp_Yquilibrium_Yq_dot___redArg(v_inst_14_, v_p_15_, v_z_16_);
return v___x_17_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Yquilibrium_Yquilibrium_Imports(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Yquilibrium_Yquilibrium_Basic(uint8_t builtin) {
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
res = initialize_Yquilibrium_Yquilibrium_Imports(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
