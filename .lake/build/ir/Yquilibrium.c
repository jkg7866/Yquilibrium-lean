// Lean compiler output
// Module: Yquilibrium
// Imports: public import Init public meta import Init public import Yquilibrium.Theorem1 public import Yquilibrium.Roots public import Yquilibrium.Welfare2 public import Yquilibrium.Duality public import Yquilibrium.DeadLoss public import Yquilibrium.EisenbergGale public import Yquilibrium.Replica public import Yquilibrium.Dynamic public import Yquilibrium.Convergence public import Yquilibrium.Berge public import Yquilibrium.Calculus public import Yquilibrium.Step1 public import Yquilibrium.ProbLemma public import Yquilibrium.Measurable public import Yquilibrium.Theorem4 public import Yquilibrium.Existence
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
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Yquilibrium_Yquilibrium_Theorem1(uint8_t builtin);
lean_object* initialize_Yquilibrium_Yquilibrium_Roots(uint8_t builtin);
lean_object* initialize_Yquilibrium_Yquilibrium_Welfare2(uint8_t builtin);
lean_object* initialize_Yquilibrium_Yquilibrium_Duality(uint8_t builtin);
lean_object* initialize_Yquilibrium_Yquilibrium_DeadLoss(uint8_t builtin);
lean_object* initialize_Yquilibrium_Yquilibrium_EisenbergGale(uint8_t builtin);
lean_object* initialize_Yquilibrium_Yquilibrium_Replica(uint8_t builtin);
lean_object* initialize_Yquilibrium_Yquilibrium_Dynamic(uint8_t builtin);
lean_object* initialize_Yquilibrium_Yquilibrium_Convergence(uint8_t builtin);
lean_object* initialize_Yquilibrium_Yquilibrium_Berge(uint8_t builtin);
lean_object* initialize_Yquilibrium_Yquilibrium_Calculus(uint8_t builtin);
lean_object* initialize_Yquilibrium_Yquilibrium_Step1(uint8_t builtin);
lean_object* initialize_Yquilibrium_Yquilibrium_ProbLemma(uint8_t builtin);
lean_object* initialize_Yquilibrium_Yquilibrium_Measurable(uint8_t builtin);
lean_object* initialize_Yquilibrium_Yquilibrium_Theorem4(uint8_t builtin);
lean_object* initialize_Yquilibrium_Yquilibrium_Existence(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Yquilibrium_Yquilibrium(uint8_t builtin) {
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
res = initialize_Yquilibrium_Yquilibrium_Theorem1(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Yquilibrium_Yquilibrium_Roots(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Yquilibrium_Yquilibrium_Welfare2(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Yquilibrium_Yquilibrium_Duality(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Yquilibrium_Yquilibrium_DeadLoss(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Yquilibrium_Yquilibrium_EisenbergGale(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Yquilibrium_Yquilibrium_Replica(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Yquilibrium_Yquilibrium_Dynamic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Yquilibrium_Yquilibrium_Convergence(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Yquilibrium_Yquilibrium_Berge(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Yquilibrium_Yquilibrium_Calculus(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Yquilibrium_Yquilibrium_Step1(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Yquilibrium_Yquilibrium_ProbLemma(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Yquilibrium_Yquilibrium_Measurable(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Yquilibrium_Yquilibrium_Theorem4(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Yquilibrium_Yquilibrium_Existence(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
