include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "c1.mm"
include "cdiv.mm"
include "co.mm"
include "wceq.mm"
include "cmul.mm"
include "wb.mm"
include "1cnd.mm"
include "simprl.mm"
include "simpll.mm"
include "simplr.mm"
include "divmul2.mm"
include "syl112anc.mm"
include "simprr.mm"
include "divmul3.mm"
include "bitr4d.mm"

theorem rec11r
  let cA: class A
  let cB: class B


  assert |- ( ( ( A e. CC /\ A =/= 0 ) /\ ( B e. CC /\ B =/= 0 ) ) -> ( ( 1 / A ) = B <-> ( 1 / B ) = A ) )

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
    #
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
    c1
    cA
    cdiv
    co
    cB
    wceq
    #
    c1
    cA
    cB
    cmul
    co
    wceq
    #
    c1
    cB
    cdiv
    co
    cA
    wceq
    #
    @6
    c1
    cc
    wcel
    #
    @3
    @0
    @1
    @7
    @8
    wb
    @6
    1cnd
    #
    @2
    @3
    @4
    simprl
    #
    @0
    @1
    @5
    simpll
    #
    @0
    @1
    @5
    simplr
    c1
    cB
    cA
    divmul2
    syl112anc
    @6
    @10
    @0
    @3
    @4
    @9
    @8
    wb
    @11
    @13
    @12
    @2
    @3
    @4
    simprr
    c1
    cA
    cB
    divmul3
    syl112anc
    bitr4d
end
