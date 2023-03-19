include "crn.mm"
include "cmap.mm"
include "co.mm"
include "cima.mm"
include "cvv.mm"
include "wcel.mm"
include "wss.mm"
include "cpm.mm"
include "wf.mm"
include "wfn.mm"
include "cv.mm"
include "cfv.mm"
include "wral.mm"
include "mrsubff.mm"
include "ffn.mm"
include "syl.mm"
include "wa.mm"
include "cdm.mm"
include "cs1.mm"
include "cif.mm"
include "cmpt.mm"
include "cmcn.mm"
include "cun.mm"
include "cfrmd.mm"
include "ccom.mm"
include "cgsu.mm"
include "wceq.mm"
include "eleq1.mm"
include "fveq2.mm"
include "s1eq.mm"
include "ifbieq12d.mm"
include "eqid.mm"
include "fvex.mm"
include "cword.mm"
include "s1cli.mm"
include "elexi.mm"
include "ifex.mm"
include "fvmpt.mm"
include "adantl.mm"
include "ifeq1da.mm"
include "ifan.mm"
include "syl6eqr.mm"
include "elpmi.mm"
include "simprd.mm"
include "sseld.mm"
include "pm4.71rd.mm"
include "bicomd.mm"
include "ifbid.mm"
include "eqtr2d.mm"
include "mpteq2dv.mm"
include "coeq1d.mm"
include "oveq2d.mm"
include "mrsubfval.mm"
include "simpld.mm"
include "adantr.mm"
include "ffvelrnda.mm"
include "wn.mm"
include "elun2.mm"
include "ad2antlr.mm"
include "s1cld.mm"
include "mrexval.mm"
include "ad3antrrr.mm"
include "eleqtrrd.mm"
include "ifclda.mm"
include "fmptd.mm"
include "ssid.mm"
include "sylancl.mm"
include "3eqtr4d.mm"
include "mapsspm.mm"
include "a1i.mm"
include "cmrex.mm"
include "eqeltri.mm"
include "cmvar.mm"
include "elmap.mm"
include "sylibr.mm"
include "fnfvima.mm"
include "syl3anc.mm"
include "eqeltrd.mm"
include "ralrimiva.mm"
include "ffnfv.mm"
include "sylanbrc.mm"
include "frn.mm"
include "c0.mm"
include "cmrsub.mm"
include "fvprc.mm"
include "syl5eq.mm"
include "rneqd.mm"
include "rn0.mm"
include "syl6eq.mm"
include "0ss.mm"
include "syl6eqss.mm"
include "pm2.61i.mm"
include "imassrn.mm"
include "eqssi.mm"

theorem mrsubrn
  let cR: class R
  let cS: class S
  let cT: class T
  let cV: class V
  let ve: setvar e
  let vf: setvar f
  let vg: setvar g
  let vv: setvar v
  let vx: setvar x
  let cW: class W
  assume mrsubvr.v: |- V = ( mVR ` T )
  assume mrsubvr.r: |- R = ( mREx ` T )
  assume mrsubvr.s: |- S = ( mRSubst ` T )


  assert |- ran S = ( S " ( R ^m V ) )

  proof
    cS
    crn
    #
    cS
    cR
    cV
    cmap
    co
    #
    cima
    #
    cT
    cvv
    wcel
    #
    @0
    @2
    wss
    #
    @3
    cR
    cV
    cpm
    co
    #
    @2
    cS
    wf
    #
    @4
    @3
    cS
    @5
    wfn
    #
    vf
    cv
    #
    cS
    cfv
    #
    @2
    wcel
    #
    vf
    @5
    wral
    @6
    @3
    @5
    cR
    cR
    cmap
    co
    #
    cS
    wf
    @7
    cR
    cS
    cT
    cV
    cvv
    mrsubvr.v
    mrsubvr.r
    mrsubvr.s
    mrsubff
    @5
    @11
    cS
    ffn
    syl
    #
    @3
    @10
    vf
    @5
    @3
    @8
    @5
    wcel
    #
    wa
    #
    @9
    vx
    cV
    vx
    cv
    #
    @8
    cdm
    #
    wcel
    #
    @15
    @8
    cfv
    #
    @15
    cs1
    #
    cif
    #
    cmpt
    #
    cS
    cfv
    #
    @2
    @14
    ve
    cR
    cT
    cmcn
    cfv
    #
    cV
    cun
    #
    cfrmd
    cfv
    #
    vv
    @24
    vv
    cv
    #
    @16
    wcel
    #
    @26
    @8
    cfv
    #
    @26
    cs1
    #
    cif
    #
    cmpt
    #
    ve
    cv
    #
    ccom
    #
    cgsu
    co
    #
    cmpt
    #
    ve
    cR
    @25
    vv
    @24
    @26
    cV
    wcel
    #
    @26
    @21
    cfv
    #
    @29
    cif
    #
    cmpt
    #
    @32
    ccom
    #
    cgsu
    co
    #
    cmpt
    #
    @9
    @22
    @14
    ve
    cR
    @34
    @41
    @14
    @33
    @40
    @25
    cgsu
    @14
    @31
    @39
    @32
    @14
    vv
    @24
    @30
    @38
    @14
    @38
    @36
    @27
    wa
    #
    @28
    @29
    cif
    #
    @30
    @14
    @38
    @36
    @30
    @29
    cif
    @44
    @14
    @36
    @37
    @30
    @29
    @36
    @37
    @30
    wceq
    @14
    vx
    @26
    @20
    @30
    cV
    @21
    @15
    @26
    wceq
    @17
    @27
    @18
    @19
    @28
    @29
    @15
    @26
    @16
    eleq1
    @15
    @26
    @8
    fveq2
    @15
    @26
    s1eq
    ifbieq12d
    @21
    eqid
    #
    @27
    @28
    @29
    @26
    @8
    fvex
    @29
    cvv
    cword
    @26
    s1cli
    elexi
    ifex
    fvmpt
    adantl
    ifeq1da
    @36
    @27
    @28
    @29
    ifan
    syl6eqr
    @14
    @43
    @27
    @28
    @29
    @14
    @27
    @43
    @14
    @27
    @36
    @14
    @16
    cV
    @26
    @14
    @16
    cR
    @8
    wf
    #
    @16
    cV
    wss
    #
    @13
    @46
    @47
    wa
    #
    @3
    cR
    cV
    @8
    elpmi
    adantl
    #
    simprd
    sseld
    pm4.71rd
    bicomd
    ifbid
    eqtr2d
    mpteq2dv
    coeq1d
    oveq2d
    mpteq2dv
    @14
    @48
    @9
    @35
    wceq
    @49
    vv
    @16
    @23
    cR
    cS
    cT
    ve
    @8
    @25
    cV
    @23
    eqid
    #
    mrsubvr.v
    mrsubvr.r
    mrsubvr.s
    @25
    eqid
    #
    mrsubfval
    syl
    @14
    cV
    cR
    @21
    wf
    #
    cV
    cV
    wss
    @22
    @42
    wceq
    @14
    vx
    cV
    @20
    cR
    @21
    @14
    @15
    cV
    wcel
    #
    wa
    #
    @17
    @18
    @19
    cR
    @54
    @16
    cR
    @15
    @8
    @14
    @46
    @53
    @14
    @46
    @47
    @49
    simpld
    adantr
    ffvelrnda
    @54
    @17
    wn
    #
    wa
    #
    @19
    @24
    cword
    #
    cR
    @56
    @15
    @24
    @53
    @15
    @24
    wcel
    @14
    @55
    @15
    cV
    @23
    elun2
    ad2antlr
    s1cld
    @3
    cR
    @57
    wceq
    @13
    @53
    @55
    @23
    cR
    cT
    cV
    cvv
    @50
    mrsubvr.v
    mrsubvr.r
    mrexval
    ad3antrrr
    eleqtrrd
    ifclda
    @45
    fmptd
    #
    cV
    ssid
    vv
    cV
    @23
    cR
    cS
    cT
    ve
    @21
    @25
    cV
    @50
    mrsubvr.v
    mrsubvr.r
    mrsubvr.s
    @51
    mrsubfval
    sylancl
    3eqtr4d
    @14
    @7
    @1
    @5
    wss
    #
    @21
    @1
    wcel
    #
    @22
    @2
    wcel
    @3
    @7
    @13
    @12
    adantr
    @59
    @14
    cR
    cV
    mapsspm
    a1i
    @14
    @52
    @60
    @58
    cR
    cV
    @21
    cR
    cT
    cmrex
    cfv
    cvv
    mrsubvr.r
    cT
    cmrex
    fvex
    eqeltri
    cV
    cT
    cmvar
    cfv
    cvv
    mrsubvr.v
    cT
    cmvar
    fvex
    eqeltri
    elmap
    sylibr
    @5
    @1
    cS
    @21
    fnfvima
    syl3anc
    eqeltrd
    ralrimiva
    vf
    @5
    @2
    cS
    ffnfv
    sylanbrc
    @5
    @2
    cS
    frn
    syl
    @3
    wn
    #
    @0
    c0
    @2
    @61
    @0
    c0
    crn
    c0
    @61
    cS
    c0
    @61
    cS
    cT
    cmrsub
    cfv
    c0
    mrsubvr.s
    cT
    cmrsub
    fvprc
    syl5eq
    rneqd
    rn0
    syl6eq
    @2
    0ss
    syl6eqss
    pm2.61i
    cS
    @1
    imassrn
    eqssi
end
