include "wf1.mm"
include "wss.mm"
include "wa.mm"
include "cima.mm"
include "cv.mm"
include "wcel.mm"
include "wi.mm"
include "simplrl.mm"
include "sseld.mm"
include "cfv.mm"
include "simplr.mm"
include "wb.mm"
include "simplll.mm"
include "simpr.mm"
include "simp1rl.mm"
include "3expa.mm"
include "f1elima.mm"
include "syl3anc.mm"
include "simp1rr.mm"
include "3imtr3d.mm"
include "ex.mm"
include "syld.mm"
include "pm2.43d.mm"
include "ssrdv.mm"
include "imass2.mm"
include "impbid1.mm"

theorem f1imass
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cF: class F
  let va: setvar a


  assert |- ( ( F : A -1-1-> B /\ ( C C_ A /\ D C_ A ) ) -> ( ( F " C ) C_ ( F " D ) <-> C C_ D ) )

  proof
    cA
    cB
    cF
    wf1
    #
    cC
    cA
    wss
    #
    cD
    cA
    wss
    #
    wa
    #
    wa
    #
    cF
    cC
    cima
    #
    cF
    cD
    cima
    #
    wss
    #
    cC
    cD
    wss
    #
    @4
    @7
    @8
    @4
    @7
    wa
    #
    va
    cC
    cD
    @9
    va
    cv
    #
    cC
    wcel
    #
    @10
    cD
    wcel
    #
    @9
    @11
    @10
    cA
    wcel
    #
    @11
    @12
    wi
    #
    @9
    cC
    cA
    @10
    @0
    @1
    @2
    @7
    simplrl
    sseld
    @9
    @13
    @14
    @9
    @13
    wa
    #
    @10
    cF
    cfv
    #
    @5
    wcel
    #
    @16
    @6
    wcel
    #
    @11
    @12
    @15
    @5
    @6
    @16
    @4
    @7
    @13
    simplr
    sseld
    @15
    @0
    @13
    @1
    @17
    @11
    wb
    @0
    @3
    @7
    @13
    simplll
    #
    @9
    @13
    simpr
    #
    @4
    @7
    @13
    @1
    @1
    @2
    @0
    @7
    @13
    simp1rl
    3expa
    cA
    cB
    cF
    @10
    cC
    f1elima
    syl3anc
    @15
    @0
    @13
    @2
    @18
    @12
    wb
    @19
    @20
    @4
    @7
    @13
    @2
    @1
    @2
    @0
    @7
    @13
    simp1rr
    3expa
    cA
    cB
    cF
    @10
    cD
    f1elima
    syl3anc
    3imtr3d
    ex
    syld
    pm2.43d
    ssrdv
    ex
    cC
    cD
    cF
    imass2
    impbid1
end
