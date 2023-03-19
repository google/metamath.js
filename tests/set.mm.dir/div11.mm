include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "w3a.mm"
include "cdiv.mm"
include "co.mm"
include "cmul.mm"
include "wceq.mm"
include "simp1.mm"
include "simp3l.mm"
include "simp3r.mm"
include "divcl.mm"
include "syl3anc.mm"
include "simp2.mm"
include "mulcand.mm"
include "divcan2.mm"
include "eqeq12d.mm"
include "bitr3d.mm"

theorem div11
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. CC /\ B e. CC /\ ( C e. CC /\ C =/= 0 ) ) -> ( ( A / C ) = ( B / C ) <-> A = B ) )

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
    cC
    cA
    cC
    cdiv
    co
    #
    cmul
    co
    #
    cC
    cB
    cC
    cdiv
    co
    #
    cmul
    co
    #
    wceq
    @6
    @8
    wceq
    cA
    cB
    wceq
    @5
    @6
    @8
    cC
    @5
    @0
    @2
    @3
    @6
    cc
    wcel
    @0
    @1
    @4
    simp1
    #
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
    cA
    cC
    divcl
    syl3anc
    @5
    @1
    @2
    @3
    @8
    cc
    wcel
    @0
    @1
    @4
    simp2
    #
    @11
    @12
    cB
    cC
    divcl
    syl3anc
    @11
    @12
    mulcand
    @5
    @7
    cA
    @9
    cB
    @5
    @0
    @2
    @3
    @7
    cA
    wceq
    @10
    @11
    @12
    cA
    cC
    divcan2
    syl3anc
    @5
    @1
    @2
    @3
    @9
    cB
    wceq
    @13
    @11
    @12
    cB
    cC
    divcan2
    syl3anc
    eqeq12d
    bitr3d
end
