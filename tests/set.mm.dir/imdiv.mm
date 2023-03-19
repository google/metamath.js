include "cc.mm"
include "wcel.mm"
include "cr.mm"
include "cc0.mm"
include "wne.mm"
include "w3a.mm"
include "c1.mm"
include "cdiv.mm"
include "co.mm"
include "cmul.mm"
include "cim.mm"
include "cfv.mm"
include "wa.mm"
include "wceq.mm"
include "ancom.mm"
include "3anass.mm"
include "bitr4i.mm"
include "rereccl.mm"
include "anim1i.mm"
include "sylbir.mm"
include "immul2.mm"
include "syl.mm"
include "recn.mm"
include "divrec2.mm"
include "fveq2d.mm"
include "syl3an2.mm"
include "imcl.mm"
include "recnd.mm"
include "3ad2ant1.mm"
include "3ad2ant2.mm"
include "simp3.mm"
include "divrec2d.mm"
include "3eqtr4d.mm"

theorem imdiv
  let cA: class A
  let cB: class B


  assert |- ( ( A e. CC /\ B e. RR /\ B =/= 0 ) -> ( Im ` ( A / B ) ) = ( ( Im ` A ) / B ) )

  proof
    cA
    cc
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
    c1
    cB
    cdiv
    co
    #
    cA
    cmul
    co
    #
    cim
    cfv
    #
    @4
    cA
    cim
    cfv
    #
    cmul
    co
    #
    cA
    cB
    cdiv
    co
    #
    cim
    cfv
    #
    @7
    cB
    cdiv
    co
    @3
    @4
    cr
    wcel
    #
    @0
    wa
    #
    @6
    @8
    wceq
    @3
    @1
    @2
    wa
    #
    @0
    wa
    #
    @12
    @14
    @0
    @13
    wa
    @3
    @13
    @0
    ancom
    @0
    @1
    @2
    3anass
    bitr4i
    @13
    @11
    @0
    cB
    rereccl
    anim1i
    sylbir
    @4
    cA
    immul2
    syl
    @1
    @0
    cB
    cc
    wcel
    #
    @2
    @10
    @6
    wceq
    cB
    recn
    #
    @0
    @15
    @2
    w3a
    @9
    @5
    cim
    cA
    cB
    divrec2
    fveq2d
    syl3an2
    @3
    @7
    cB
    @0
    @1
    @7
    cc
    wcel
    @2
    @0
    @7
    cA
    imcl
    recnd
    3ad2ant1
    @1
    @0
    @15
    @2
    @16
    3ad2ant2
    @0
    @1
    @2
    simp3
    divrec2d
    3eqtr4d
end
