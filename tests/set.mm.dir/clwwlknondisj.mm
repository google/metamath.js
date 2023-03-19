include "cv.mm"
include "cclwwlknon.mm"
include "cfv.mm"
include "co.mm"
include "wdisj.mm"
include "weq.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "wo.mm"
include "wral.mm"
include "wn.mm"
include "cc0.mm"
include "cclwwlkn.mm"
include "crab.mm"
include "clwwlknon.mm"
include "ineq12i.mm"
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
include "oveq1.mm"
include "disjor.mm"
include "mpbir.mm"

theorem clwwlknondisj
  let vx: setvar x
  let cG: class G
  let cN: class N
  let cV: class V
  let vw: setvar w
  let vy: setvar y

  disjoint G x
  disjoint N x
  disjoint V x
  disjoint G w
  disjoint G y
  disjoint w x
  disjoint w y
  disjoint x y
  disjoint N w
  disjoint N y
  disjoint V y
  assert |- Disj_ x e. V ( x ( ClWWalksNOn ` G ) N )

  proof
    vx
    cV
    vx
    cv
    #
    cN
    cG
    cclwwlknon
    cfv
    #
    co
    #
    wdisj
    vx
    vy
    weq
    #
    @2
    vy
    cv
    #
    cN
    @1
    co
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
    @8
    vx
    vy
    cV
    cV
    @3
    @7
    @3
    wn
    #
    @6
    cc0
    vw
    cv
    cfv
    #
    @0
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
    @10
    @4
    wceq
    #
    vw
    @12
    crab
    #
    cin
    #
    c0
    @2
    @13
    @5
    @15
    vw
    cG
    cN
    @0
    clwwlknon
    vw
    cG
    cN
    @4
    clwwlknon
    ineq12i
    @9
    @16
    @11
    @14
    wa
    #
    vw
    @12
    crab
    #
    c0
    @11
    @14
    vw
    @12
    inrab
    @9
    @17
    wn
    #
    vw
    @12
    wral
    @18
    c0
    wceq
    @9
    @19
    vw
    @12
    @17
    @3
    @10
    @0
    @4
    eqtr2
    con3i
    ralrimivw
    @17
    vw
    @12
    rabeq0
    sylibr
    syl5eq
    syl5eq
    orri
    rgen2w
    cV
    @2
    @5
    vx
    vy
    @0
    @4
    cN
    @1
    oveq1
    disjor
    mpbir
end
