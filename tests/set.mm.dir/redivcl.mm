include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "w3a.mm"
include "cdiv.mm"
include "co.mm"
include "c1.mm"
include "cmul.mm"
include "cc.mm"
include "wceq.mm"
include "simp1.mm"
include "recnd.mm"
include "simp2.mm"
include "simp3.mm"
include "divrec.mm"
include "syl3anc.mm"
include "rereccl.mm"
include "3adant1.mm"
include "remulcld.mm"
include "eqeltrd.mm"

theorem redivcl
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR /\ B e. RR /\ B =/= 0 ) -> ( A / B ) e. RR )

  proof
    cA
    cr
    wcel
    #
    cB
    cr
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
    #
    cA
    c1
    cB
    cdiv
    co
    #
    cmul
    co
    #
    cr
    @3
    cA
    cc
    wcel
    cB
    cc
    wcel
    @2
    @4
    @6
    wceq
    @3
    cA
    @0
    @1
    @2
    simp1
    #
    recnd
    @3
    cB
    @0
    @1
    @2
    simp2
    recnd
    @0
    @1
    @2
    simp3
    cA
    cB
    divrec
    syl3anc
    @3
    cA
    @5
    @7
    @1
    @2
    @5
    cr
    wcel
    @0
    cB
    rereccl
    3adant1
    remulcld
    eqeltrd
end
