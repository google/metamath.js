include "crp.mm"
include "wcel.mm"
include "csqrt.mm"
include "cfv.mm"
include "cmul.mm"
include "co.mm"
include "cdiv.mm"
include "cr.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "wceq.mm"
include "rpre.mm"
include "rpge0.mm"
include "remsqsqrt.mm"
include "syl2anc.mm"
include "oveq1d.mm"
include "recnd.mm"
include "sqrtcld.mm"
include "rpsqrtcl.mm"
include "rpne0d.mm"
include "divcan4d.mm"
include "eqtr3d.mm"

theorem divsqrtid
  let cA: class A


  assert |- ( A e. RR+ -> ( A / ( sqrt ` A ) ) = ( sqrt ` A ) )

  proof
    cA
    crp
    wcel
    #
    cA
    csqrt
    cfv
    #
    @1
    cmul
    co
    #
    @1
    cdiv
    co
    cA
    @1
    cdiv
    co
    @1
    @0
    @2
    cA
    @1
    cdiv
    @0
    cA
    cr
    wcel
    cc0
    cA
    cle
    wbr
    @2
    cA
    wceq
    cA
    rpre
    #
    cA
    rpge0
    cA
    remsqsqrt
    syl2anc
    oveq1d
    @0
    @1
    @1
    @0
    cA
    @0
    cA
    @3
    recnd
    sqrtcld
    #
    @4
    @0
    @1
    cA
    rpsqrtcl
    rpne0d
    divcan4d
    eqtr3d
end
