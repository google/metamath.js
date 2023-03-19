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
include "reccl.mm"
include "adantl.mm"
include "simpl.mm"
include "divmul.mm"
include "syl3anc.mm"
include "simpll.mm"
include "simprl.mm"
include "simprr.mm"
include "divrec.mm"
include "eqeq1d.mm"
include "diveq1.mm"
include "3bitr2d.mm"

theorem rec11
  let cA: class A
  let cB: class B


  assert |- ( ( ( A e. CC /\ A =/= 0 ) /\ ( B e. CC /\ B =/= 0 ) ) -> ( ( 1 / A ) = ( 1 / B ) <-> A = B ) )

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
    c1
    cB
    cdiv
    co
    #
    wceq
    #
    cA
    @7
    cmul
    co
    #
    c1
    wceq
    #
    cA
    cB
    cdiv
    co
    #
    c1
    wceq
    #
    cA
    cB
    wceq
    #
    @6
    c1
    cc
    wcel
    @7
    cc
    wcel
    #
    @2
    @8
    @10
    wb
    @6
    1cnd
    @5
    @14
    @2
    cB
    reccl
    adantl
    @2
    @5
    simpl
    c1
    @7
    cA
    divmul
    syl3anc
    @6
    @11
    @9
    c1
    @6
    @0
    @3
    @4
    @11
    @9
    wceq
    @0
    @1
    @5
    simpll
    #
    @2
    @3
    @4
    simprl
    #
    @2
    @3
    @4
    simprr
    #
    cA
    cB
    divrec
    syl3anc
    eqeq1d
    @6
    @0
    @3
    @4
    @12
    @13
    wb
    @15
    @16
    @17
    cA
    cB
    diveq1
    syl3anc
    3bitr2d
end
