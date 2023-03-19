include "wcel.mm"
include "cn0.mm"
include "cfv.mm"
include "c1o.mm"
include "cv.mm"
include "csn.mm"
include "cxp.mm"
include "cmpt.mm"
include "coe1fval.mm"
include "fveq1d.mm"
include "wceq.mm"
include "sneq.mm"
include "xpeq2d.mm"
include "fveq2d.mm"
include "eqid.mm"
include "fvex.mm"
include "fvmpt.mm"
include "sylan9eq.mm"

theorem coe1fv
  let cA: class A
  let cF: class F
  let cN: class N
  let cV: class V
  let vn: setvar n
  let vf: setvar f
  assume coe1fval.a: |- A = ( coe1 ` F )


  assert |- ( ( F e. V /\ N e. NN0 ) -> ( A ` N ) = ( F ` ( 1o X. { N } ) ) )

  proof
    cF
    cV
    wcel
    #
    cN
    cn0
    wcel
    cN
    cA
    cfv
    cN
    vn
    cn0
    c1o
    vn
    cv
    #
    csn
    #
    cxp
    #
    cF
    cfv
    #
    cmpt
    #
    cfv
    c1o
    cN
    csn
    #
    cxp
    #
    cF
    cfv
    #
    @0
    cN
    cA
    @5
    cA
    vn
    cF
    cV
    coe1fval.a
    coe1fval
    fveq1d
    vn
    cN
    @4
    @8
    cn0
    @5
    @1
    cN
    wceq
    #
    @3
    @7
    cF
    @9
    @2
    @6
    c1o
    @1
    cN
    sneq
    xpeq2d
    fveq2d
    @5
    eqid
    @7
    cF
    fvex
    fvmpt
    sylan9eq
end
