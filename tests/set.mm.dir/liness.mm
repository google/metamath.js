include "cn.mm"
include "wcel.mm"
include "cee.mm"
include "cfv.mm"
include "wne.mm"
include "w3a.mm"
include "wa.mm"
include "cline2.mm"
include "co.mm"
include "cv.mm"
include "cop.mm"
include "ccolin.mm"
include "wbr.mm"
include "cab.mm"
include "fvline.mm"
include "cvv.mm"
include "wi.mm"
include "vex.mm"
include "a1i.mm"
include "simp1.mm"
include "simp2.mm"
include "3jca.mm"
include "colineardim1.mm"
include "sylan2.mm"
include "abssdv.mm"
include "eqsstrd.mm"

theorem liness
  let cA: class A
  let cB: class B
  let cN: class N
  let vx: setvar x


  assert |- ( ( N e. NN /\ ( A e. ( EE ` N ) /\ B e. ( EE ` N ) /\ A =/= B ) ) -> ( A Line B ) C_ ( EE ` N ) )

  proof
    cN
    cn
    wcel
    #
    cA
    cN
    cee
    cfv
    #
    wcel
    #
    cB
    @1
    wcel
    #
    cA
    cB
    wne
    #
    w3a
    #
    wa
    #
    cA
    cB
    cline2
    co
    vx
    cv
    #
    cA
    cB
    cop
    ccolin
    wbr
    #
    vx
    cab
    @1
    vx
    cA
    cB
    cN
    fvline
    @6
    @8
    vx
    @1
    @5
    @0
    @7
    cvv
    wcel
    #
    @2
    @3
    w3a
    @8
    @7
    @1
    wcel
    wi
    @5
    @9
    @2
    @3
    @9
    @5
    vx
    vex
    a1i
    @2
    @3
    @4
    simp1
    @2
    @3
    @4
    simp2
    3jca
    @7
    cA
    cB
    cN
    cvv
    @1
    colineardim1
    sylan2
    abssdv
    eqsstrd
end
