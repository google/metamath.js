include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "w3a.mm"
include "cdiv.mm"
include "co.mm"
include "ccj.mm"
include "cfv.mm"
include "cmul.mm"
include "divcl.mm"
include "cjcl.mm"
include "syl.mm"
include "simp2.mm"
include "simp3.mm"
include "wb.mm"
include "cjne0.mm"
include "mpbid.mm"
include "divcan4d.mm"
include "wceq.mm"
include "cjmul.mm"
include "syl2anc.mm"
include "divcan1.mm"
include "fveq2d.mm"
include "eqtr3d.mm"
include "oveq1d.mm"

theorem cjdiv
  let cA: class A
  let cB: class B


  assert |- ( ( A e. CC /\ B e. CC /\ B =/= 0 ) -> ( * ` ( A / B ) ) = ( ( * ` A ) / ( * ` B ) ) )

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
    ccj
    cfv
    #
    cB
    ccj
    cfv
    #
    cmul
    co
    #
    @6
    cdiv
    co
    @5
    cA
    ccj
    cfv
    #
    @6
    cdiv
    co
    @3
    @5
    @6
    @3
    @4
    cc
    wcel
    #
    @5
    cc
    wcel
    cA
    cB
    divcl
    #
    @4
    cjcl
    syl
    @3
    @1
    @6
    cc
    wcel
    @0
    @1
    @2
    simp2
    #
    cB
    cjcl
    syl
    @3
    @2
    @6
    cc0
    wne
    #
    @0
    @1
    @2
    simp3
    @3
    @1
    @2
    @12
    wb
    @11
    cB
    cjne0
    syl
    mpbid
    divcan4d
    @3
    @7
    @8
    @6
    cdiv
    @3
    @4
    cB
    cmul
    co
    #
    ccj
    cfv
    #
    @7
    @8
    @3
    @9
    @1
    @14
    @7
    wceq
    @10
    @11
    @4
    cB
    cjmul
    syl2anc
    @3
    @13
    cA
    ccj
    cA
    cB
    divcan1
    fveq2d
    eqtr3d
    oveq1d
    eqtr3d
end
