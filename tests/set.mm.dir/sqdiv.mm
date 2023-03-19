include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "w3a.mm"
include "cdiv.mm"
include "co.mm"
include "cmul.mm"
include "c2.mm"
include "cexp.mm"
include "wa.mm"
include "wceq.mm"
include "simp1.mm"
include "3simpc.mm"
include "divmuldiv.mm"
include "syl22anc.mm"
include "divcl.mm"
include "sqval.mm"
include "syl.mm"
include "oveqan12d.mm"
include "3adant3.mm"
include "3eqtr4d.mm"

theorem sqdiv
  let cA: class A
  let cB: class B


  assert |- ( ( A e. CC /\ B e. CC /\ B =/= 0 ) -> ( ( A / B ) ^ 2 ) = ( ( A ^ 2 ) / ( B ^ 2 ) ) )

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
    #
    @4
    cmul
    co
    #
    cA
    cA
    cmul
    co
    #
    cB
    cB
    cmul
    co
    #
    cdiv
    co
    #
    @4
    c2
    cexp
    co
    #
    cA
    c2
    cexp
    co
    #
    cB
    c2
    cexp
    co
    #
    cdiv
    co
    #
    @3
    @0
    @0
    @1
    @2
    wa
    #
    @13
    @5
    @8
    wceq
    @0
    @1
    @2
    simp1
    #
    @14
    @0
    @1
    @2
    3simpc
    #
    @15
    cA
    cA
    cB
    cB
    divmuldiv
    syl22anc
    @3
    @4
    cc
    wcel
    @9
    @5
    wceq
    cA
    cB
    divcl
    @4
    sqval
    syl
    @0
    @1
    @12
    @8
    wceq
    @2
    @0
    @1
    @10
    @6
    @11
    @7
    cdiv
    cA
    sqval
    cB
    sqval
    oveqan12d
    3adant3
    3eqtr4d
end
