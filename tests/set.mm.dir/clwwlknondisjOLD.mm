include "cc0.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "cclwwlkn.mm"
include "co.mm"
include "crab.mm"
include "wdisj.mm"
include "weq.mm"
include "cin.mm"
include "c0.mm"
include "wo.mm"
include "wral.mm"
include "wn.mm"
include "wa.mm"
include "inrab.mm"
include "eqtr2.mm"
include "con3i.mm"
include "ralrimivw.mm"
include "rabeq0.mm"
include "sylibr.mm"
include "syl5eq.mm"
include "orri.mm"
include "rgen2w.mm"
include "eqeq2.mm"
include "rabbidv.mm"
include "disjor.mm"
include "mpbir.mm"

theorem clwwlknondisjOLD
  let vx: setvar x
  let vw: setvar w
  let cG: class G
  let cN: class N
  let cV: class V
  let vy: setvar y

  disjoint G x
  disjoint N x
  disjoint V x
  disjoint w x
  disjoint G y
  disjoint x y
  disjoint N y
  disjoint V y
  disjoint w y
  assert |- Disj_ x e. V { w e. ( N ClWWalksN G ) | ( w ` 0 ) = x }

  proof
    vx
    cV
    cc0
    vw
    cv
    cfv
    #
    vx
    cv
    #
    wceq
    #
    vw
    cN
    cG
    cclwwlkn
    co
    #
    crab
    #
    wdisj
    vx
    vy
    weq
    #
    @4
    @0
    vy
    cv
    #
    wceq
    #
    vw
    @3
    crab
    #
    cin
    #
    c0
    wceq
    #
    wo
    #
    vy
    cV
    wral
    vx
    cV
    wral
    @11
    vx
    vy
    cV
    cV
    @5
    @10
    @5
    wn
    #
    @9
    @2
    @7
    wa
    #
    vw
    @3
    crab
    #
    c0
    @2
    @7
    vw
    @3
    inrab
    @12
    @13
    wn
    #
    vw
    @3
    wral
    @14
    c0
    wceq
    @12
    @15
    vw
    @3
    @13
    @5
    @0
    @1
    @6
    eqtr2
    con3i
    ralrimivw
    @13
    vw
    @3
    rabeq0
    sylibr
    syl5eq
    orri
    rgen2w
    cV
    @4
    @8
    vx
    vy
    @5
    @2
    @7
    vw
    @3
    @1
    @6
    @0
    eqeq2
    rabbidv
    disjor
    mpbir
end
