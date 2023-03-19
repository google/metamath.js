include "clly.mm"
include "wcel.mm"
include "ctop.mm"
include "cv.mm"
include "crest.mm"
include "co.mm"
include "csn.mm"
include "cnei.mm"
include "cfv.mm"
include "cpw.mm"
include "cin.mm"
include "wrex.mm"
include "wral.mm"
include "cnlly.mm"
include "llytop.mm"
include "w3a.mm"
include "wss.mm"
include "llyi.mm"
include "wa.mm"
include "simpl1.mm"
include "syl.mm"
include "simprl.mm"
include "simprr2.mm"
include "opnneip.mm"
include "syl3anc.mm"
include "simprr1.mm"
include "selpw.mm"
include "sylibr.mm"
include "elind.mm"
include "simprr3.mm"
include "jca.mm"
include "ex.mm"
include "reximdv2.mm"
include "mpd.mm"
include "3expb.mm"
include "ralrimivva.mm"
include "isnlly.mm"
include "sylanbrc.mm"

theorem llynlly
  let cA: class A
  let cJ: class J
  let vj: setvar j
  let vs: setvar s
  let vu: setvar u
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let cP: class P
  let cU: class U
  let cV: class V


  assert |- ( J e. Locally A -> J e. N-Locally A )

  proof
    cJ
    cA
    clly
    wcel
    #
    cJ
    ctop
    wcel
    #
    cJ
    vu
    cv
    #
    crest
    co
    cA
    wcel
    #
    vu
    vy
    cv
    #
    csn
    cJ
    cnei
    cfv
    cfv
    #
    vx
    cv
    #
    cpw
    #
    cin
    #
    wrex
    #
    vy
    @6
    wral
    vx
    cJ
    wral
    cJ
    cA
    cnlly
    wcel
    cA
    cJ
    llytop
    #
    @0
    @9
    vx
    vy
    cJ
    @6
    @0
    @6
    cJ
    wcel
    #
    @4
    @6
    wcel
    #
    @9
    @0
    @11
    @12
    w3a
    #
    @2
    @6
    wss
    #
    @4
    @2
    wcel
    #
    @3
    w3a
    #
    vu
    cJ
    wrex
    @9
    vu
    cA
    @4
    @6
    cJ
    llyi
    @13
    @16
    @3
    vu
    cJ
    @8
    @13
    @2
    cJ
    wcel
    #
    @16
    wa
    #
    @2
    @8
    wcel
    #
    @3
    wa
    @13
    @18
    wa
    #
    @19
    @3
    @20
    @5
    @7
    @2
    @20
    @1
    @17
    @15
    @2
    @5
    wcel
    @20
    @0
    @1
    @0
    @11
    @12
    @18
    simpl1
    @10
    syl
    @13
    @17
    @16
    simprl
    @14
    @15
    @3
    @17
    @13
    simprr2
    @4
    cJ
    @2
    opnneip
    syl3anc
    @20
    @14
    @2
    @7
    wcel
    @14
    @15
    @3
    @17
    @13
    simprr1
    vu
    @6
    selpw
    sylibr
    elind
    @14
    @15
    @3
    @17
    @13
    simprr3
    jca
    ex
    reximdv2
    mpd
    3expb
    ralrimivva
    vx
    vy
    vu
    cA
    cJ
    isnlly
    sylanbrc
end
