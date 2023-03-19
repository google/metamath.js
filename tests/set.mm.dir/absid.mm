include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
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
include "simpl.mm"
include "recnd.mm"
include "absval.mm"
include "syl.mm"
include "cjred.mm"
include "oveq2d.mm"
include "sqvald.mm"
include "eqtr4d.mm"
include "fveq2d.mm"
include "sqrtsq.mm"
include "3eqtrd.mm"

theorem absid
  let cA: class A


  assert |- ( ( A e. RR /\ 0 <_ A ) -> ( abs ` A ) = A )

  proof
    cA
    cr
    wcel
    #
    cc0
    cA
    cle
    wbr
    #
    wa
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
    cA
    @2
    cA
    cc
    wcel
    @3
    @6
    wceq
    @2
    cA
    @0
    @1
    simpl
    #
    recnd
    #
    cA
    absval
    syl
    @2
    @5
    @7
    csqrt
    @2
    @5
    cA
    cA
    cmul
    co
    @7
    @2
    @4
    cA
    cA
    cmul
    @2
    cA
    @8
    cjred
    oveq2d
    @2
    cA
    @9
    sqvald
    eqtr4d
    fveq2d
    cA
    sqrtsq
    3eqtrd
end
