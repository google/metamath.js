include "cc.mm"
include "cxp.mm"
include "cmul.mm"
include "wf.mm"
include "wfn.mm"
include "cv.mm"
include "co.mm"
include "wcel.mm"
include "wral.mm"
include "wfun.mm"
include "cdm.mm"
include "wceq.mm"
include "wa.mm"
include "cop.mm"
include "cmr.mm"
include "cm1r.mm"
include "cplr.mm"
include "wex.mm"
include "coprab.mm"
include "wmo.mm"
include "moeq.mm"
include "mosubop.mm"
include "anass.mm"
include "2exbii.mm"
include "19.42vv.mm"
include "bitri.mm"
include "mobii.mm"
include "mpbir.mm"
include "moani.mm"
include "funoprab.mm"
include "df-mul.mm"
include "funeqi.mm"
include "dmeqi.mm"
include "dmoprabss.mm"
include "eqsstri.mm"
include "0ncn.mm"
include "cnr.mm"
include "df-c.mm"
include "oveq1.mm"
include "eleq1d.mm"
include "oveq2.mm"
include "mulcnsr.mm"
include "mulclsr.mm"
include "m1r.mm"
include "sylancr.mm"
include "addclsr.mm"
include "syl2an.mm"
include "an4s.mm"
include "syl2anr.mm"
include "an42s.mm"
include "opelxpi.mm"
include "syl2anc.mm"
include "eqeltrd.mm"
include "2optocl.mm"
include "syl6eleqr.mm"
include "oprssdm.mm"
include "eqssi.mm"
include "df-fn.mm"
include "mpbir2an.mm"
include "rgen2a.mm"
include "ffnov.mm"

theorem axmulf
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  let vu: setvar u
  let vf: setvar f


  assert |- x. : ( CC X. CC ) --> CC

  proof
    cc
    cc
    cxp
    #
    cc
    cmul
    wf
    cmul
    @0
    wfn
    #
    vx
    cv
    #
    vy
    cv
    #
    cmul
    co
    #
    cc
    wcel
    #
    vy
    cc
    wral
    vx
    cc
    wral
    @1
    cmul
    wfun
    #
    cmul
    cdm
    #
    @0
    wceq
    @6
    @2
    cc
    wcel
    @3
    cc
    wcel
    wa
    #
    @2
    vw
    cv
    #
    vv
    cv
    #
    cop
    wceq
    #
    @3
    vu
    cv
    #
    vf
    cv
    #
    cop
    wceq
    #
    wa
    vz
    cv
    #
    @9
    @12
    cmr
    co
    #
    cm1r
    @10
    @13
    cmr
    co
    cmr
    co
    cplr
    co
    @10
    @12
    cmr
    co
    @9
    @13
    cmr
    co
    cplr
    co
    cop
    #
    wceq
    #
    wa
    #
    vf
    wex
    vu
    wex
    #
    vv
    wex
    vw
    wex
    #
    wa
    #
    vx
    vy
    vz
    coprab
    #
    wfun
    @22
    vx
    vy
    vz
    @21
    @8
    vz
    @21
    vz
    wmo
    @11
    @14
    @18
    wa
    #
    vf
    wex
    vu
    wex
    #
    wa
    #
    vv
    wex
    vw
    wex
    #
    vz
    wmo
    @25
    vz
    vw
    vv
    @2
    @18
    vz
    vu
    vf
    @3
    vz
    @17
    moeq
    mosubop
    mosubop
    @21
    @27
    vz
    @20
    @26
    vw
    vv
    @20
    @11
    @24
    wa
    #
    vf
    wex
    vu
    wex
    @26
    @19
    @28
    vu
    vf
    @11
    @14
    @18
    anass
    2exbii
    @11
    @24
    vu
    vf
    19.42vv
    bitri
    2exbii
    mobii
    mpbir
    moani
    funoprab
    cmul
    @23
    vx
    vy
    vz
    vw
    vv
    vu
    vf
    df-mul
    #
    funeqi
    mpbir
    @7
    @0
    @7
    @23
    cdm
    @0
    cmul
    @23
    @29
    dmeqi
    @21
    vx
    vy
    vz
    cc
    cc
    dmoprabss
    eqsstri
    vx
    vy
    cc
    cmul
    0ncn
    @8
    @4
    cnr
    cnr
    cxp
    #
    cc
    @15
    @9
    cop
    #
    @10
    @12
    cop
    #
    cmul
    co
    #
    @30
    wcel
    @2
    @32
    cmul
    co
    #
    @30
    wcel
    @4
    @30
    wcel
    vz
    vw
    vv
    vu
    @2
    @3
    cnr
    cnr
    cc
    df-c
    @31
    @2
    wceq
    @33
    @34
    @30
    @31
    @2
    @32
    cmul
    oveq1
    eleq1d
    @32
    @3
    wceq
    @34
    @4
    @30
    @32
    @3
    @2
    cmul
    oveq2
    eleq1d
    @15
    cnr
    wcel
    #
    @9
    cnr
    wcel
    #
    wa
    @10
    cnr
    wcel
    #
    @12
    cnr
    wcel
    #
    wa
    wa
    #
    @33
    @15
    @10
    cmr
    co
    #
    cm1r
    @16
    cmr
    co
    #
    cplr
    co
    #
    @9
    @10
    cmr
    co
    #
    @15
    @12
    cmr
    co
    #
    cplr
    co
    #
    cop
    #
    @30
    @15
    @9
    @10
    @12
    mulcnsr
    @39
    @42
    cnr
    wcel
    #
    @45
    cnr
    wcel
    #
    @46
    @30
    wcel
    @35
    @37
    @36
    @38
    @47
    @35
    @37
    wa
    @40
    cnr
    wcel
    @41
    cnr
    wcel
    #
    @47
    @36
    @38
    wa
    #
    @15
    @10
    mulclsr
    @50
    cm1r
    cnr
    wcel
    @16
    cnr
    wcel
    @49
    m1r
    @9
    @12
    mulclsr
    cm1r
    @16
    mulclsr
    sylancr
    @40
    @41
    addclsr
    syl2an
    an4s
    @35
    @38
    @36
    @37
    @48
    @36
    @37
    wa
    @43
    cnr
    wcel
    @44
    cnr
    wcel
    @48
    @35
    @38
    wa
    @9
    @10
    mulclsr
    @15
    @12
    mulclsr
    @43
    @44
    addclsr
    syl2anr
    an42s
    @42
    @45
    cnr
    cnr
    opelxpi
    syl2anc
    eqeltrd
    2optocl
    df-c
    syl6eleqr
    #
    oprssdm
    eqssi
    cmul
    @0
    df-fn
    mpbir2an
    @5
    vx
    vy
    cc
    @51
    rgen2a
    vx
    vy
    cc
    cc
    cc
    cmul
    ffnov
    mpbir2an
end
