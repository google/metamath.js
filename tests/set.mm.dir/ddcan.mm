include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "cdiv.mm"
include "co.mm"
include "wceq.mm"
include "cmul.mm"
include "simpll.mm"
include "simprl.mm"
include "simprr.mm"
include "divcan1.mm"
include "syl3anc.mm"
include "wb.mm"
include "divcl.mm"
include "divne0.mm"
include "divmul.mm"
include "syl112anc.mm"
include "mpbird.mm"

theorem ddcan
  let cA: class A
  let cB: class B


  assert |- ( ( ( A e. CC /\ A =/= 0 ) /\ ( B e. CC /\ B =/= 0 ) ) -> ( A / ( A / B ) ) = B )

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
    cA
    cA
    cB
    cdiv
    co
    #
    cdiv
    co
    cB
    wceq
    #
    @7
    cB
    cmul
    co
    cA
    wceq
    #
    @6
    @0
    @3
    @4
    @9
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
    divcan1
    syl3anc
    @6
    @0
    @3
    @7
    cc
    wcel
    #
    @7
    cc0
    wne
    @8
    @9
    wb
    @10
    @11
    @6
    @0
    @3
    @4
    @13
    @10
    @11
    @12
    cA
    cB
    divcl
    syl3anc
    cA
    cB
    divne0
    cA
    cB
    @7
    divmul
    syl112anc
    mpbird
end
