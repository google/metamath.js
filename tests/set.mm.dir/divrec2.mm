include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "w3a.mm"
include "cdiv.mm"
include "co.mm"
include "c1.mm"
include "cmul.mm"
include "divrec.mm"
include "simp1.mm"
include "reccl.mm"
include "3adant1.mm"
include "mulcomd.mm"
include "eqtrd.mm"

theorem divrec2
  let cA: class A
  let cB: class B


  assert |- ( ( A e. CC /\ B e. CC /\ B =/= 0 ) -> ( A / B ) = ( ( 1 / B ) x. A ) )

  proof
    cA
    cc
    wcel
    #
    cB
    cc
    wcel
    #
    cB
    cc0
    wne
    #
    w3a
    #
    cA
    cB
    cdiv
    co
    cA
    c1
    cB
    cdiv
    co
    #
    cmul
    co
    @4
    cA
    cmul
    co
    cA
    cB
    divrec
    @3
    cA
    @4
    @0
    @1
    @2
    simp1
    @1
    @2
    @4
    cc
    wcel
    @0
    cB
    reccl
    3adant1
    mulcomd
    eqtrd
end
