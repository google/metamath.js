include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "cdiv.mm"
include "co.mm"
include "c1.mm"
include "cmul.mm"
include "recdiv.mm"
include "oveq2d.mm"
include "wceq.mm"
include "divcl.mm"
include "3expb.mm"
include "adantlr.mm"
include "divne0.mm"
include "recid.mm"
include "syl2anc.mm"
include "eqtr3d.mm"

theorem divcan6
  let cA: class A
  let cB: class B


  assert |- ( ( ( A e. CC /\ A =/= 0 ) /\ ( B e. CC /\ B =/= 0 ) ) -> ( ( A / B ) x. ( B / A ) ) = 1 )

  proof
    cA
    cc
    wcel
    #
    cA
    cc0
    wne
    #
    wa
    cB
    cc
    wcel
    #
    cB
    cc0
    wne
    #
    wa
    #
    wa
    #
    cA
    cB
    cdiv
    co
    #
    c1
    @6
    cdiv
    co
    #
    cmul
    co
    #
    @6
    cB
    cA
    cdiv
    co
    #
    cmul
    co
    c1
    @5
    @7
    @9
    @6
    cmul
    cA
    cB
    recdiv
    oveq2d
    @5
    @6
    cc
    wcel
    #
    @6
    cc0
    wne
    @8
    c1
    wceq
    @0
    @4
    @10
    @1
    @0
    @2
    @3
    @10
    cA
    cB
    divcl
    3expb
    adantlr
    cA
    cB
    divne0
    @6
    recid
    syl2anc
    eqtr3d
end
