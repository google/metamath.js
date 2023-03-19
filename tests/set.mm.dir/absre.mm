include "cr.mm"
include "wcel.mm"
include "cabs.mm"
include "cfv.mm"
include "ccj.mm"
include "cmul.mm"
include "co.mm"
include "csqrt.mm"
include "c2.mm"
include "cexp.mm"
include "cc.mm"
include "wceq.mm"
include "recn.mm"
include "absval.mm"
include "syl.mm"
include "sqvald.mm"
include "cjre.mm"
include "oveq2d.mm"
include "eqtr4d.mm"
include "fveq2d.mm"

theorem absre
  let cA: class A


  assert |- ( A e. RR -> ( abs ` A ) = ( sqrt ` ( A ^ 2 ) ) )

  proof
    cA
    cr
    wcel
    #
    cA
    cabs
    cfv
    #
    cA
    cA
    ccj
    cfv
    #
    cmul
    co
    #
    csqrt
    cfv
    #
    cA
    c2
    cexp
    co
    #
    csqrt
    cfv
    @0
    cA
    cc
    wcel
    @1
    @4
    wceq
    cA
    recn
    #
    cA
    absval
    syl
    @0
    @5
    @3
    csqrt
    @0
    @5
    cA
    cA
    cmul
    co
    @3
    @0
    cA
    @6
    sqvald
    @0
    @2
    cA
    cA
    cmul
    cA
    cjre
    oveq2d
    eqtr4d
    fveq2d
    eqtr4d
end
