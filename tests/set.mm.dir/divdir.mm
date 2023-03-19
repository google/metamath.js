include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "w3a.mm"
include "caddc.mm"
include "co.mm"
include "c1.mm"
include "cdiv.mm"
include "cmul.mm"
include "simp1.mm"
include "simp2.mm"
include "reccl.mm"
include "3ad2ant3.mm"
include "adddird.mm"
include "wceq.mm"
include "addcld.mm"
include "simp3l.mm"
include "simp3r.mm"
include "divrec.mm"
include "syl3anc.mm"
include "oveq12d.mm"
include "3eqtr4d.mm"

theorem divdir
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. CC /\ B e. CC /\ ( C e. CC /\ C =/= 0 ) ) -> ( ( A + B ) / C ) = ( ( A / C ) + ( B / C ) ) )

  proof
    cA
    cc
    wcel
    #
    cB
    cc
    wcel
    #
    cC
    cc
    wcel
    #
    cC
    cc0
    wne
    #
    wa
    #
    w3a
    #
    cA
    cB
    caddc
    co
    #
    c1
    cC
    cdiv
    co
    #
    cmul
    co
    #
    cA
    @7
    cmul
    co
    #
    cB
    @7
    cmul
    co
    #
    caddc
    co
    @6
    cC
    cdiv
    co
    #
    cA
    cC
    cdiv
    co
    #
    cB
    cC
    cdiv
    co
    #
    caddc
    co
    @5
    cA
    cB
    @7
    @0
    @1
    @4
    simp1
    #
    @0
    @1
    @4
    simp2
    #
    @4
    @0
    @7
    cc
    wcel
    @1
    cC
    reccl
    3ad2ant3
    adddird
    @5
    @6
    cc
    wcel
    @2
    @3
    @11
    @8
    wceq
    @5
    cA
    cB
    @14
    @15
    addcld
    @0
    @1
    @2
    @3
    simp3l
    #
    @0
    @1
    @2
    @3
    simp3r
    #
    @6
    cC
    divrec
    syl3anc
    @5
    @12
    @9
    @13
    @10
    caddc
    @5
    @0
    @2
    @3
    @12
    @9
    wceq
    @14
    @16
    @17
    cA
    cC
    divrec
    syl3anc
    @5
    @1
    @2
    @3
    @13
    @10
    wceq
    @15
    @16
    @17
    cB
    cC
    divrec
    syl3anc
    oveq12d
    3eqtr4d
end
