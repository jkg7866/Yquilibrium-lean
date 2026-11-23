// Lean compiler output
// Module: Yquilibrium.CES2
// Imports: public import Init public meta import Init public import Yquilibrium.Roots public import Mathlib.Analysis.SpecialFunctions.Pow.Real public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
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
LEAN_EXPORT lean_object* lp_Yquilibrium_Yq_prefOf___redArg();
LEAN_EXPORT lean_object* lp_Yquilibrium_Yq_prefOf___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_Yquilibrium_Yq_prefOf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Yquilibrium_Yq_prefOf___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Yquilibrium_Yq_prefOf___redArg(){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_box(0);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* lp_Yquilibrium_Yq_prefOf___redArg___boxed(lean_object* v___dummy_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = lp_Yquilibrium_Yq_prefOf___redArg();
return v_res_4_;
}
}
LEAN_EXPORT lean_object* lp_Yquilibrium_Yq_prefOf(lean_object* v_K_5_, lean_object* v_inst_6_, lean_object* v_inst_7_, lean_object* v_U_8_, lean_object* v_hc_9_, lean_object* v_hm_10_){
_start:
{
lean_object* v___x_11_; 
v___x_11_ = lean_box(0);
return v___x_11_;
}
}
LEAN_EXPORT lean_object* lp_Yquilibrium_Yq_prefOf___boxed(lean_object* v_K_12_, lean_object* v_inst_13_, lean_object* v_inst_14_, lean_object* v_U_15_, lean_object* v_hc_16_, lean_object* v_hm_17_){
_start:
{
lean_object* v_res_18_; 
v_res_18_ = lp_Yquilibrium_Yq_prefOf(v_K_12_, v_inst_13_, v_inst_14_, v_U_15_, v_hc_16_, v_hm_17_);
lean_dec(v_U_15_);
lean_dec(v_inst_13_);
return v_res_18_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Yquilibrium_Yquilibrium_Roots(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Analysis_SpecialFunctions_Pow_Real(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Analysis_SpecialFunctions_Pow_Continuity(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Yquilibrium_Yquilibrium_CES2(uint8_t builtin) {
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
res = initialize_Yquilibrium_Yquilibrium_Roots(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Analysis_SpecialFunctions_Pow_Real(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Analysis_SpecialFunctions_Pow_Continuity(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
