include "wcel.mm"
include "cvv.mm"
include "cn0.mm"
include "c1o.mm"
include "cv.mm"
include "csn.mm"
include "cxp.mm"
include "cfv.mm"
include "cmpt.mm"
include "wceq.mm"
include "elex.mm"
include "cco1.mm"
include "fveq1.mm"
include "mpteq2dv.mm"
include "df-coe1.mm"
include "nn0ex.mm"
include "mptex.mm"
include "fvmpt.mm"
include "syl5eq.mm"
include "syl.mm"

theorem coe1fval
  let cA: class A
  let vn: setvar n
  let cF: class F
  let cV: class V
  let vf: setvar f
  assume coe1fval.a: |- A = ( coe1 ` F )

  disjoint F n
  disjoint F f
  disjoint f n
  assert |- ( F e. V -> A = ( n e. NN0 |-> ( F ` ( 1o X. { n } ) ) ) )

  proof
    cF
    cV
    wcel
    cF
    cvv
    wcel
    #
    cA
    vn
    cn0
    c1o
    vn
    cv
    csn
    cxp
    #
    cF
    cfv
    #
    cmpt
    #
    wceq
    cF
    cV
    elex
    @0
    cA
    cF
    cco1
    cfv
    @3
    coe1fval.a
    vf
    cF
    vn
    cn0
    @1
    vf
    cv
    #
    cfv
    #
    cmpt
    @3
    cvv
    cco1
    @4
    cF
    wceq
    vn
    cn0
    @5
    @2
    @1
    @4
    cF
    fveq1
    mpteq2dv
    vf
    vn
    df-coe1
    vn
    cn0
    @2
    nn0ex
    mptex
    fvmpt
    syl5eq
    syl
end
