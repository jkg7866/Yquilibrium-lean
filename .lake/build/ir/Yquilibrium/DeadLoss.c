// Lean compiler output
// Module: Yquilibrium.DeadLoss
// Imports: public import Init public meta import Init public import Yquilibrium.Welfare2
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
LEAN_EXPORT lean_object* lp_Yquilibrium_Yq_Economy_Ssum___redArg();
LEAN_EXPORT lean_object* lp_Yquilibrium_Yq_Economy_Ssum___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_Yquilibrium_Yq_Economy_Ssum(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Yquilibrium_Yq_Economy_Ssum___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Yquilibrium_Yq_Economy_Tset___redArg();
LEAN_EXPORT lean_object* lp_Yquilibrium_Yq_Economy_Tset___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_Yquilibrium_Yq_Economy_Tset(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Yquilibrium_Yq_Economy_Tset___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Yquilibrium_Yq_Economy_Ssum___redArg(){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_box(0);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* lp_Yquilibrium_Yq_Economy_Ssum___redArg___boxed(lean_object* v___dummy_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = lp_Yquilibrium_Yq_Economy_Ssum___redArg();
return v_res_4_;
}
}
LEAN_EXPORT lean_object* lp_Yquilibrium_Yq_Economy_Ssum(lean_object* v_K_5_, lean_object* v_inst_6_, lean_object* v_N_7_, lean_object* v_inst_8_, lean_object* v_E_9_, lean_object* v_x_10_){
_start:
{
lean_object* v___x_11_; 
v___x_11_ = lean_box(0);
return v___x_11_;
}
}
LEAN_EXPORT lean_object* lp_Yquilibrium_Yq_Economy_Ssum___boxed(lean_object* v_K_12_, lean_object* v_inst_13_, lean_object* v_N_14_, lean_object* v_inst_15_, lean_object* v_E_16_, lean_object* v_x_17_){
_start:
{
lean_object* v_res_18_; 
v_res_18_ = lp_Yquilibrium_Yq_Economy_Ssum(v_K_12_, v_inst_13_, v_N_14_, v_inst_15_, v_E_16_, v_x_17_);
lean_dec(v_x_17_);
lean_dec_ref(v_E_16_);
lean_dec(v_inst_15_);
lean_dec(v_inst_13_);
return v_res_18_;
}
}
LEAN_EXPORT lean_object* lp_Yquilibrium_Yq_Economy_Tset___redArg(){
_start:
{
lean_object* v___x_20_; 
v___x_20_ = lean_box(0);
return v___x_20_;
}
}
LEAN_EXPORT lean_object* lp_Yquilibrium_Yq_Economy_Tset___redArg___boxed(lean_object* v___dummy_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = lp_Yquilibrium_Yq_Economy_Tset___redArg();
return v_res_22_;
}
}
LEAN_EXPORT lean_object* lp_Yquilibrium_Yq_Economy_Tset(lean_object* v_K_23_, lean_object* v_inst_24_, lean_object* v_N_25_, lean_object* v_inst_26_, lean_object* v_E_27_, lean_object* v_x_28_){
_start:
{
lean_object* v___x_29_; 
v___x_29_ = lean_box(0);
return v___x_29_;
}
}
LEAN_EXPORT lean_object* lp_Yquilibrium_Yq_Economy_Tset___boxed(lean_object* v_K_30_, lean_object* v_inst_31_, lean_object* v_N_32_, lean_object* v_inst_33_, lean_object* v_E_34_, lean_object* v_x_35_){
_start:
{
lean_object* v_res_36_; 
v_res_36_ = lp_Yquilibrium_Yq_Economy_Tset(v_K_30_, v_inst_31_, v_N_32_, v_inst_33_, v_E_34_, v_x_35_);
lean_dec(v_x_35_);
lean_dec_ref(v_E_34_);
lean_dec(v_inst_33_);
lean_dec(v_inst_31_);
return v_res_36_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Yquilibrium_Yquilibrium_Welfare2(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Yquilibrium_Yquilibrium_DeadLoss(uint8_t builtin) {
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
res = initialize_Yquilibrium_Yquilibrium_Welfare2(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
