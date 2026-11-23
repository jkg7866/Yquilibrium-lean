// Lean compiler output
// Module: Yquilibrium.Theorem1
// Imports: public import Init public meta import Init public import Yquilibrium.Basic
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
LEAN_EXPORT lean_object* lp_Yquilibrium_Yq_Economy_W___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Yquilibrium_Yq_Economy_W___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Yquilibrium_Yq_Economy_W(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Yquilibrium_Yq_Economy_W___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Yquilibrium_Yq_Economy_Prices___redArg();
LEAN_EXPORT lean_object* lp_Yquilibrium_Yq_Economy_Prices___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_Yquilibrium_Yq_Economy_Prices(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Yquilibrium_Yq_Economy_Prices___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Yquilibrium_Yq_Economy_W___redArg___lam__0(lean_object* v_E_1_, lean_object* v_k_2_, lean_object* v_i_3_){
_start:
{
lean_object* v_00_u03c9_4_; lean_object* v___x_5_; 
v_00_u03c9_4_ = lean_ctor_get(v_E_1_, 1);
lean_inc(v_00_u03c9_4_);
lean_dec_ref(v_E_1_);
v___x_5_ = lean_apply_2(v_00_u03c9_4_, v_i_3_, v_k_2_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* lp_Yquilibrium_Yq_Economy_W___redArg(lean_object* v_inst_6_, lean_object* v_E_7_, lean_object* v_k_8_){
_start:
{
lean_object* v___f_9_; lean_object* v___x_10_; lean_object* v___x_11_; 
v___f_9_ = lean_alloc_closure((void*)(lp_Yquilibrium_Yq_Economy_W___redArg___lam__0), 3, 2);
lean_closure_set(v___f_9_, 0, v_E_7_);
lean_closure_set(v___f_9_, 1, v_k_8_);
v___x_10_ = lp_mathlib_Real_instAddCommMonoid;
v___x_11_ = lp_mathlib_Finset_sum___redArg(v___x_10_, v_inst_6_, v___f_9_);
return v___x_11_;
}
}
LEAN_EXPORT lean_object* lp_Yquilibrium_Yq_Economy_W(lean_object* v_K_12_, lean_object* v_inst_13_, lean_object* v_N_14_, lean_object* v_inst_15_, lean_object* v_E_16_, lean_object* v_k_17_){
_start:
{
lean_object* v___x_18_; 
v___x_18_ = lp_Yquilibrium_Yq_Economy_W___redArg(v_inst_15_, v_E_16_, v_k_17_);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* lp_Yquilibrium_Yq_Economy_W___boxed(lean_object* v_K_19_, lean_object* v_inst_20_, lean_object* v_N_21_, lean_object* v_inst_22_, lean_object* v_E_23_, lean_object* v_k_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = lp_Yquilibrium_Yq_Economy_W(v_K_19_, v_inst_20_, v_N_21_, v_inst_22_, v_E_23_, v_k_24_);
lean_dec(v_inst_20_);
return v_res_25_;
}
}
LEAN_EXPORT lean_object* lp_Yquilibrium_Yq_Economy_Prices___redArg(){
_start:
{
lean_object* v___x_27_; 
v___x_27_ = lean_box(0);
return v___x_27_;
}
}
LEAN_EXPORT lean_object* lp_Yquilibrium_Yq_Economy_Prices___redArg___boxed(lean_object* v___dummy_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = lp_Yquilibrium_Yq_Economy_Prices___redArg();
return v_res_29_;
}
}
LEAN_EXPORT lean_object* lp_Yquilibrium_Yq_Economy_Prices(lean_object* v_K_30_, lean_object* v_inst_31_, lean_object* v_N_32_, lean_object* v_inst_33_, lean_object* v_E_34_){
_start:
{
lean_object* v___x_35_; 
v___x_35_ = lean_box(0);
return v___x_35_;
}
}
LEAN_EXPORT lean_object* lp_Yquilibrium_Yq_Economy_Prices___boxed(lean_object* v_K_36_, lean_object* v_inst_37_, lean_object* v_N_38_, lean_object* v_inst_39_, lean_object* v_E_40_){
_start:
{
lean_object* v_res_41_; 
v_res_41_ = lp_Yquilibrium_Yq_Economy_Prices(v_K_36_, v_inst_37_, v_N_38_, v_inst_39_, v_E_40_);
lean_dec_ref(v_E_40_);
lean_dec(v_inst_39_);
lean_dec(v_inst_37_);
return v_res_41_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Yquilibrium_Yquilibrium_Basic(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Yquilibrium_Yquilibrium_Theorem1(uint8_t builtin) {
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
res = initialize_Yquilibrium_Yquilibrium_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
