include "cnrm.mm"
include "wcel.mm"
include "ckq.mm"
include "cfv.mm"
include "ct1.mm"
include "wa.mm"
include "ctop.mm"
include "wel.mm"
include "cv.mm"
include "ccl.mm"
include "wss.mm"
include "wrex.mm"
include "wral.mm"
include "creg.mm"
include "nrmtop.mm"
include "adantr.mm"
include "wb.mm"
include "cuni.mm"
include "crab.mm"
include "ccld.mm"
include "simpll.mm"
include "simprl.mm"
include "ctopon.mm"
include "eqid.mm"
include "toptopon.mm"
include "sylib.mm"
include "simplr.mm"
include "simprr.mm"
include "elunii.mm"
include "syl2anc.mm"
include "cmpt.mm"
include "r0cld.mm"
include "syl3anc.mm"
include "w3a.mm"
include "simp1rr.mm"
include "wi.mm"
include "weq.mm"
include "elequ2.mm"
include "bibi12d.mm"
include "rspcv.mm"
include "syl.mm"
include "3impia.mm"
include "mpbird.mm"
include "rabssdv.mm"
include "nrmsep3.mm"
include "syl13anc.mm"
include "biidd.mm"
include "ralrimivw.mm"
include "elequ1.mm"
include "bibi1d.mm"
include "ralbidv.mm"
include "elrab.mm"
include "sylanbrc.mm"
include "ssel.mm"
include "syl5com.mm"
include "anim1d.mm"
include "reximdv.mm"
include "mpd.mm"
include "ralrimivva.mm"
include "isreg.mm"

theorem nrmr0reg
  let cJ: class J
  let vo: setvar o
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let va: setvar a
  let vb: setvar b
  let vj: setvar j
  let vw: setvar w
  let vz: setvar z
  let cX: class X


  assert |- ( ( J e. Nrm /\ ( KQ ` J ) e. Fre ) -> J e. Reg )

  proof
    cJ
    cnrm
    wcel
    #
    cJ
    ckq
    cfv
    ct1
    wcel
    #
    wa
    #
    cJ
    ctop
    wcel
    #
    vy
    vz
    wel
    #
    vz
    cv
    #
    cJ
    ccl
    cfv
    cfv
    vx
    cv
    #
    wss
    #
    wa
    #
    vz
    cJ
    wrex
    #
    vy
    @6
    wral
    vx
    cJ
    wral
    cJ
    creg
    wcel
    @0
    @3
    @1
    cJ
    nrmtop
    adantr
    #
    @2
    @9
    vx
    vy
    cJ
    @6
    @2
    @6
    cJ
    wcel
    #
    vy
    vx
    wel
    #
    wa
    #
    wa
    #
    va
    vb
    wel
    #
    vy
    vb
    wel
    #
    wb
    #
    vb
    cJ
    wral
    #
    va
    cJ
    cuni
    #
    crab
    #
    @5
    wss
    #
    @7
    wa
    #
    vz
    cJ
    wrex
    #
    @9
    @14
    @0
    @11
    @20
    cJ
    ccld
    cfv
    wcel
    #
    @20
    @6
    wss
    @23
    @0
    @1
    @13
    simpll
    @2
    @11
    @12
    simprl
    #
    @14
    cJ
    @19
    ctopon
    cfv
    wcel
    #
    @1
    vy
    cv
    #
    @19
    wcel
    #
    @24
    @14
    @3
    @26
    @2
    @3
    @13
    @10
    adantr
    cJ
    @19
    @19
    eqid
    toptopon
    sylib
    @0
    @1
    @13
    simplr
    @14
    @12
    @11
    @28
    @2
    @11
    @12
    simprr
    @25
    @27
    @6
    cJ
    elunii
    syl2anc
    #
    vz
    vw
    va
    @27
    vb
    vz
    @19
    vz
    vw
    wel
    vw
    cJ
    crab
    cmpt
    #
    cJ
    @19
    @30
    eqid
    r0cld
    syl3anc
    @14
    @18
    va
    @19
    @6
    @14
    va
    cv
    @19
    wcel
    #
    @18
    w3a
    va
    vx
    wel
    #
    @12
    @11
    @12
    @2
    @31
    @18
    simp1rr
    @14
    @31
    @18
    @32
    @12
    wb
    #
    @14
    @31
    wa
    @11
    @18
    @33
    wi
    @14
    @11
    @31
    @25
    adantr
    @17
    @33
    vb
    @6
    cJ
    vb
    vx
    weq
    @15
    @32
    @16
    @12
    vb
    vx
    va
    elequ2
    vb
    vx
    vy
    elequ2
    bibi12d
    rspcv
    syl
    3impia
    mpbird
    rabssdv
    vz
    @6
    @20
    cJ
    nrmsep3
    syl13anc
    @14
    @22
    @8
    vz
    cJ
    @14
    @21
    @4
    @7
    @14
    @27
    @20
    wcel
    #
    @21
    @4
    @14
    @28
    @16
    @16
    wb
    #
    vb
    cJ
    wral
    #
    @34
    @29
    @14
    @35
    vb
    cJ
    @14
    @16
    biidd
    ralrimivw
    @18
    @36
    va
    @27
    @19
    va
    vy
    weq
    #
    @17
    @35
    vb
    cJ
    @37
    @15
    @16
    @16
    va
    vy
    vb
    elequ1
    bibi1d
    ralbidv
    elrab
    sylanbrc
    @20
    @5
    @27
    ssel
    syl5com
    anim1d
    reximdv
    mpd
    ralrimivva
    vx
    vy
    vz
    cJ
    isreg
    sylanbrc
end
