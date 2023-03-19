include "cc.mm"
include "ce.mm"
include "cdv.mm"
include "co.mm"
include "wceq.mm"
include "wtru.mm"
include "cv.mm"
include "cfv.mm"
include "cmpt.mm"
include "wf.mm"
include "cdm.mm"
include "dvfcn.mm"
include "dvbsss.mm"
include "wcel.mm"
include "wbr.mm"
include "csn.mm"
include "cxp.mm"
include "cmin.mm"
include "cmul.mm"
include "cof.mm"
include "cc0.mm"
include "c1.mm"
include "caddc.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "efcl.mm"
include "fconstg.mm"
include "syl.mm"
include "snssd.mm"
include "fssd.mm"
include "wss.mm"
include "ssid.mm"
include "a1i.mm"
include "wa.mm"
include "subcl.mm"
include "ancoms.mm"
include "eqid.mm"
include "fmptd.mm"
include "0cn.mm"
include "ax-1cn.mm"
include "cop.mm"
include "elexi.mm"
include "snid.mm"
include "opelxpi.mm"
include "mpan2.mm"
include "dvconst.mm"
include "eleqtrrd.mm"
include "df-br.mm"
include "sylibr.mm"
include "ccom.mm"
include "eff.mm"
include "oveq1.mm"
include "ovex.mm"
include "fvmpt.mm"
include "subid.mm"
include "eqtrd.mm"
include "dveflem.mm"
include "syl6eqbr.mm"
include "cr.mm"
include "cpr.mm"
include "cnelprrecn.mm"
include "simpr.mm"
include "dvmptid.mm"
include "simpl.mm"
include "id.mm"
include "dvmptc.mm"
include "dvmptsub.mm"
include "1m0e1.mm"
include "mpteq2i.mm"
include "fconstmpt.mm"
include "eqtr4i.mm"
include "syl6eq.mm"
include "dvcobr.mm"
include "1t1e1.mm"
include "syl6breq.mm"
include "eqidd.mm"
include "feqmptd.mm"
include "fveq2.mm"
include "fmptco.mm"
include "oveq2d.mm"
include "breqd.mm"
include "mpbid.mm"
include "dvmulbr.mm"
include "ffvelrnd.mm"
include "mul02d.mm"
include "fvex.mm"
include "fvconst2.mm"
include "mulid2d.mm"
include "oveq12d.mm"
include "addid2d.mm"
include "breqtrd.mm"
include "cvv.mm"
include "cnex.mm"
include "offval2.mm"
include "efadd.mm"
include "syldan.mm"
include "pncan3.mm"
include "fveq2d.mm"
include "eqtr3d.mm"
include "mpteq2dva.mm"
include "eqtr4d.mm"
include "vex.mm"
include "breldm.mm"
include "ssriv.mm"
include "eqssi.mm"
include "feq2i.mm"
include "mpbi.mm"
include "wfun.mm"
include "ffun.mm"
include "ax-mp.mm"
include "funbrfv.mm"
include "mpsyl.mm"
include "mpteq2ia.mm"
include "trud.mm"

theorem dvef
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( CC _D exp ) = exp

  proof
    cc
    ce
    cdv
    co
    #
    ce
    wceq
    wtru
    @0
    vx
    cc
    vx
    cv
    #
    ce
    cfv
    #
    cmpt
    #
    ce
    wtru
    @0
    vx
    cc
    @1
    @0
    cfv
    #
    cmpt
    @3
    wtru
    vx
    cc
    cc
    @0
    cc
    cc
    @0
    wf
    #
    wtru
    @0
    cdm
    #
    cc
    @0
    wf
    #
    @5
    ce
    dvfcn
    #
    @6
    cc
    cc
    @0
    @6
    cc
    cc
    ce
    dvbsss
    vx
    cc
    @6
    @1
    cc
    wcel
    #
    @1
    @2
    @0
    wbr
    #
    @1
    @6
    wcel
    @9
    @1
    @2
    cc
    cc
    @2
    csn
    #
    cxp
    #
    vz
    cc
    vz
    cv
    #
    @1
    cmin
    co
    #
    ce
    cfv
    #
    cmpt
    #
    cmul
    cof
    co
    #
    cdv
    co
    #
    wbr
    @10
    @9
    @1
    cc0
    @1
    @16
    cfv
    #
    cmul
    co
    #
    c1
    @1
    @12
    cfv
    #
    cmul
    co
    #
    caddc
    co
    #
    @2
    @18
    @9
    @1
    cc
    @12
    @16
    ccnfld
    ctopn
    cfv
    #
    cc0
    c1
    cc
    cc
    cc
    @9
    cc
    @11
    cc
    @12
    @9
    @2
    cc
    wcel
    #
    cc
    @11
    @12
    wf
    @1
    efcl
    #
    cc
    @2
    cc
    fconstg
    syl
    @9
    @2
    cc
    @26
    snssd
    fssd
    cc
    cc
    wss
    @9
    cc
    ssid
    a1i
    #
    @9
    vz
    cc
    @15
    cc
    @16
    @9
    @13
    cc
    wcel
    #
    wa
    #
    @14
    cc
    wcel
    #
    @15
    cc
    wcel
    @28
    @9
    @30
    @13
    @1
    subcl
    ancoms
    #
    @14
    efcl
    syl
    @16
    eqid
    fmptd
    #
    @27
    @27
    cc0
    cc
    wcel
    #
    @9
    0cn
    a1i
    c1
    cc
    wcel
    #
    @9
    ax-1cn
    a1i
    #
    @9
    @1
    cc0
    cop
    #
    cc
    @12
    cdv
    co
    #
    wcel
    @1
    cc0
    @37
    wbr
    @9
    @36
    cc
    cc0
    csn
    #
    cxp
    #
    @37
    @9
    cc0
    @38
    wcel
    @36
    @39
    wcel
    cc0
    cc0
    cc
    0cn
    elexi
    snid
    @1
    cc0
    cc
    @38
    opelxpi
    mpan2
    @9
    @25
    @37
    @39
    wceq
    @26
    @2
    dvconst
    syl
    eleqtrrd
    @1
    cc0
    @37
    df-br
    sylibr
    @9
    @1
    c1
    cc
    ce
    vz
    cc
    @14
    cmpt
    #
    ccom
    #
    cdv
    co
    #
    wbr
    @1
    c1
    cc
    @16
    cdv
    co
    #
    wbr
    @9
    @1
    c1
    c1
    cmul
    co
    c1
    @42
    @9
    @1
    cc
    cc
    ce
    @40
    @24
    c1
    c1
    cc
    cc
    cc
    cc
    cc
    ce
    wf
    #
    @9
    eff
    a1i
    #
    @27
    @9
    vz
    cc
    @14
    cc
    @40
    @31
    @40
    eqid
    #
    fmptd
    @27
    @27
    @27
    @35
    @35
    @9
    @1
    @40
    cfv
    #
    cc0
    c1
    @0
    @9
    @47
    @1
    @1
    cmin
    co
    #
    cc0
    vz
    @1
    @14
    @48
    cc
    @40
    @13
    @1
    @1
    cmin
    oveq1
    @46
    @1
    @1
    cmin
    ovex
    fvmpt
    @1
    subid
    eqtrd
    dveflem
    syl6eqbr
    @9
    @1
    c1
    cop
    #
    cc
    @40
    cdv
    co
    #
    wcel
    @1
    c1
    @50
    wbr
    @9
    @49
    cc
    c1
    csn
    #
    cxp
    #
    @50
    @9
    c1
    @51
    wcel
    @49
    @52
    wcel
    c1
    c1
    cc
    ax-1cn
    elexi
    snid
    @1
    c1
    cc
    @51
    opelxpi
    mpan2
    @9
    @50
    vz
    cc
    c1
    cc0
    cmin
    co
    #
    cmpt
    #
    @52
    @9
    vz
    @13
    c1
    @1
    cc0
    cc
    cc
    cc
    cc
    cc
    cr
    cc
    cpr
    wcel
    @9
    cnelprrecn
    a1i
    #
    @9
    @28
    simpr
    @34
    @29
    ax-1cn
    a1i
    @9
    vz
    cc
    @55
    dvmptid
    @9
    @28
    simpl
    @33
    @29
    0cn
    a1i
    @9
    vz
    @1
    cc
    @55
    @9
    id
    #
    dvmptc
    dvmptsub
    @54
    vz
    cc
    c1
    cmpt
    @52
    vz
    cc
    @53
    c1
    1m0e1
    mpteq2i
    vz
    cc
    c1
    fconstmpt
    eqtr4i
    syl6eq
    eleqtrrd
    @1
    c1
    @50
    df-br
    sylibr
    @24
    eqid
    #
    dvcobr
    1t1e1
    syl6breq
    @9
    @42
    @43
    @1
    c1
    @9
    @41
    @16
    cc
    cdv
    @9
    vz
    vy
    cc
    cc
    @14
    vy
    cv
    #
    ce
    cfv
    @15
    @40
    ce
    @31
    @9
    @40
    eqidd
    @9
    vy
    cc
    cc
    ce
    @45
    feqmptd
    @58
    @14
    ce
    fveq2
    fmptco
    oveq2d
    breqd
    mpbid
    @57
    dvmulbr
    @9
    @23
    cc0
    @2
    caddc
    co
    @2
    @9
    @20
    cc0
    @22
    @2
    caddc
    @9
    @19
    @9
    cc
    cc
    @1
    @16
    @32
    @56
    ffvelrnd
    mul02d
    @9
    @22
    c1
    @2
    cmul
    co
    @2
    @9
    @21
    @2
    c1
    cmul
    cc
    @2
    @1
    @1
    ce
    fvex
    #
    fvconst2
    oveq2d
    @9
    @2
    @26
    mulid2d
    eqtrd
    oveq12d
    @9
    @2
    @26
    addid2d
    eqtrd
    breqtrd
    @9
    @18
    @0
    @1
    @2
    @9
    @17
    ce
    cc
    cdv
    @9
    @17
    vz
    cc
    @2
    @15
    cmul
    co
    #
    cmpt
    #
    ce
    @9
    vz
    cc
    @2
    @15
    cmul
    @12
    @16
    cvv
    cvv
    cvv
    cc
    cvv
    wcel
    @9
    cnex
    a1i
    @2
    cvv
    wcel
    @29
    @59
    a1i
    @15
    cvv
    wcel
    @29
    @14
    ce
    fvex
    a1i
    @12
    vz
    cc
    @2
    cmpt
    wceq
    @9
    vz
    cc
    @2
    fconstmpt
    a1i
    @9
    @16
    eqidd
    offval2
    @9
    ce
    vz
    cc
    @13
    ce
    cfv
    #
    cmpt
    @61
    @9
    vz
    cc
    cc
    ce
    @45
    feqmptd
    @9
    vz
    cc
    @60
    @62
    @29
    @1
    @14
    caddc
    co
    #
    ce
    cfv
    #
    @60
    @62
    @9
    @28
    @30
    @64
    @60
    wceq
    @31
    @1
    @14
    efadd
    syldan
    @29
    @63
    @13
    ce
    @1
    @13
    pncan3
    fveq2d
    eqtr3d
    mpteq2dva
    eqtr4d
    eqtr4d
    oveq2d
    breqd
    mpbid
    #
    @1
    @2
    @0
    vx
    vex
    @59
    breldm
    syl
    ssriv
    eqssi
    feq2i
    mpbi
    a1i
    feqmptd
    vx
    cc
    @4
    @2
    @0
    wfun
    #
    @9
    @10
    @4
    @2
    wceq
    @7
    @66
    @8
    @6
    cc
    @0
    ffun
    ax-mp
    @65
    @1
    @2
    @0
    funbrfv
    mpsyl
    mpteq2ia
    syl6eq
    wtru
    vx
    cc
    cc
    ce
    @44
    wtru
    eff
    a1i
    feqmptd
    eqtr4d
    trud
end
