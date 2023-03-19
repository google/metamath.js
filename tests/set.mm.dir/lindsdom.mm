include "cdr.mm"
include "wcel.mm"
include "cfn.mm"
include "cfrlm.mm"
include "co.mm"
include "clinds.mm"
include "cfv.mm"
include "w3a.mm"
include "cuvc.mm"
include "crn.mm"
include "cdom.mm"
include "wbr.mm"
include "cen.mm"
include "cv.mm"
include "c0.mm"
include "cun.mm"
include "clss.mm"
include "cmri.mm"
include "wa.mm"
include "cpw.mm"
include "wrex.mm"
include "cmrc.mm"
include "cbs.mm"
include "cmre.mm"
include "clmod.mm"
include "crg.mm"
include "drngring.mm"
include "eqid.mm"
include "frlmlmod.mm"
include "sylan.mm"
include "lssmre.mm"
include "syl.mm"
include "3adant3.mm"
include "csn.mm"
include "cdif.mm"
include "wral.mm"
include "cacs.mm"
include "clvec.mm"
include "csca.mm"
include "frlmsca.mm"
include "simpl.mm"
include "eqeltrrd.mm"
include "islvec.mm"
include "sylanbrc.mm"
include "lssacsex.mm"
include "simprd.mm"
include "wss.mm"
include "dif0.mm"
include "linds1.mm"
include "3ad2ant3.mm"
include "wf.mm"
include "uvcff.mm"
include "frn.mm"
include "syl6sseqr.mm"
include "wceq.mm"
include "un0.mm"
include "fveq2i.mm"
include "clspn.mm"
include "mrclsp.mm"
include "fveq1d.mm"
include "clbs.mm"
include "frlmlbs.mm"
include "lbssp.mm"
include "eqtr3d.mm"
include "syl5eq.mm"
include "sseqtr4d.mm"
include "wn.mm"
include "cnzr.mm"
include "drngnzr.mm"
include "adantr.mm"
include "jca.mm"
include "lindsind2.mm"
include "3expa.mm"
include "sylanl1.mm"
include "wb.mm"
include "eleq2d.mm"
include "ad2antrr.mm"
include "mtbid.mm"
include "ralrimiva.mm"
include "3impa.mm"
include "ismri2.mm"
include "syl2an.mm"
include "mpbird.mm"
include "syl5eqel.mm"
include "wo.mm"
include "simpr.mm"
include "uvcendim.mm"
include "enfi.mm"
include "mpbid.mm"
include "olcd.mm"
include "mreexexd.mm"
include "cvv.mm"
include "ovex.mm"
include "rnex.mm"
include "elpwi.mm"
include "ssdomg.mm"
include "mpsyl.mm"
include "endomtr.mm"
include "syl2anr.mm"
include "rexlimiva.mm"
include "ensymd.mm"
include "domentr.mm"
include "syl2anc.mm"

theorem lindsdom
  let cR: class R
  let cI: class I
  let cX: class X
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( R e. DivRing /\ I e. Fin /\ X e. ( LIndS ` ( R freeLMod I ) ) ) -> X ~<_ I )

  proof
    cR
    cdr
    wcel
    #
    cI
    cfn
    wcel
    #
    cX
    cR
    cI
    cfrlm
    co
    #
    clinds
    cfv
    wcel
    #
    w3a
    #
    cX
    cR
    cI
    cuvc
    co
    #
    crn
    #
    cdom
    wbr
    #
    @6
    cI
    cen
    wbr
    #
    cX
    cI
    cdom
    wbr
    @4
    cX
    vf
    cv
    #
    cen
    wbr
    #
    @9
    c0
    cun
    @2
    clss
    cfv
    #
    cmri
    cfv
    #
    wcel
    #
    wa
    #
    vf
    @6
    cpw
    #
    wrex
    @7
    @4
    vy
    vz
    @11
    cX
    @6
    c0
    @12
    @11
    cmrc
    cfv
    #
    @2
    cbs
    cfv
    #
    vx
    vf
    @0
    @1
    @11
    @17
    cmre
    cfv
    wcel
    #
    @3
    @0
    @1
    wa
    #
    @2
    clmod
    wcel
    #
    @18
    @0
    cR
    crg
    wcel
    #
    @1
    @20
    cR
    drngring
    #
    cR
    @2
    cI
    cfn
    @2
    eqid
    #
    frlmlmod
    sylan
    #
    @17
    @11
    @2
    @17
    eqid
    #
    @11
    eqid
    #
    lssmre
    syl
    #
    3adant3
    @16
    eqid
    #
    @12
    eqid
    #
    @0
    @1
    vy
    cv
    #
    vx
    cv
    #
    vz
    cv
    csn
    cun
    @16
    cfv
    wcel
    vz
    @31
    @30
    csn
    #
    cun
    @16
    cfv
    @31
    @16
    cfv
    cdif
    wral
    vy
    @17
    wral
    vx
    @17
    cpw
    wral
    #
    @3
    @19
    @11
    @17
    cacs
    cfv
    wcel
    #
    @33
    @19
    @2
    clvec
    wcel
    #
    @34
    @33
    wa
    @19
    @20
    @2
    csca
    cfv
    #
    cdr
    wcel
    @35
    @24
    @19
    cR
    @36
    cdr
    cR
    @2
    cI
    cdr
    cfn
    @23
    frlmsca
    #
    @0
    @1
    simpl
    eqeltrrd
    @36
    @2
    @36
    eqid
    #
    islvec
    sylanbrc
    vy
    vz
    @11
    @16
    @2
    @17
    vx
    @26
    @28
    @25
    lssacsex
    syl
    simprd
    3adant3
    @3
    @0
    cX
    @17
    c0
    cdif
    #
    wss
    @1
    @39
    @2
    cX
    @17
    dif0
    #
    linds1
    3ad2ant3
    @0
    @1
    @6
    @39
    wss
    @3
    @19
    @6
    @17
    @39
    @19
    cI
    @17
    @5
    wf
    #
    @6
    @17
    wss
    @0
    @21
    @1
    @41
    @22
    @17
    cR
    @5
    cI
    cfn
    @2
    @5
    eqid
    #
    @23
    @25
    uvcff
    sylan
    cI
    @17
    @5
    frn
    syl
    @40
    syl6sseqr
    3adant3
    @4
    cX
    @17
    @6
    c0
    cun
    #
    @16
    cfv
    #
    @3
    @0
    cX
    @17
    wss
    #
    @1
    @17
    @2
    cX
    @25
    linds1
    #
    3ad2ant3
    @0
    @1
    @44
    @17
    wceq
    @3
    @19
    @44
    @6
    @16
    cfv
    #
    @17
    @43
    @6
    @16
    @6
    un0
    fveq2i
    @19
    @6
    @2
    clspn
    cfv
    #
    cfv
    #
    @47
    @17
    @19
    @6
    @48
    @16
    @19
    @20
    @48
    @16
    wceq
    @24
    @11
    @16
    @48
    @2
    @26
    @48
    eqid
    #
    @28
    mrclsp
    syl
    #
    fveq1d
    @19
    @6
    @2
    clbs
    cfv
    #
    wcel
    #
    @49
    @17
    wceq
    @0
    @21
    @1
    @53
    @22
    cR
    @5
    @2
    cI
    @52
    cfn
    @23
    @42
    @52
    eqid
    #
    frlmlbs
    sylan
    @6
    @52
    @48
    @17
    @2
    @25
    @54
    @50
    lbssp
    syl
    eqtr3d
    syl5eq
    3adant3
    sseqtr4d
    @4
    cX
    c0
    cun
    cX
    @12
    cX
    un0
    @4
    cX
    @12
    wcel
    #
    @30
    cX
    @32
    cdif
    #
    @16
    cfv
    #
    wcel
    #
    wn
    #
    vy
    cX
    wral
    #
    @0
    @1
    @3
    @60
    @19
    @3
    wa
    #
    @59
    vy
    cX
    @61
    @30
    cX
    wcel
    #
    wa
    @30
    @56
    @48
    cfv
    #
    wcel
    #
    @58
    @19
    @20
    @36
    cnzr
    wcel
    #
    wa
    #
    @3
    @62
    @64
    wn
    #
    @19
    @20
    @65
    @24
    @19
    cR
    @36
    cnzr
    @37
    @0
    cR
    cnzr
    wcel
    #
    @1
    cR
    drngnzr
    #
    adantr
    eqeltrrd
    jca
    @66
    @3
    @62
    @67
    @30
    cX
    @48
    @36
    @2
    @50
    @38
    lindsind2
    3expa
    sylanl1
    @19
    @64
    @58
    wb
    @3
    @62
    @19
    @63
    @57
    @30
    @19
    @56
    @48
    @16
    @51
    fveq1d
    eleq2d
    ad2antrr
    mtbid
    ralrimiva
    3impa
    @0
    @1
    @3
    @55
    @60
    wb
    #
    @19
    @18
    @45
    @70
    @3
    @27
    @46
    vy
    @11
    cX
    @12
    @16
    @17
    @28
    @29
    ismri2
    syl2an
    3impa
    mpbird
    syl5eqel
    @0
    @1
    cX
    cfn
    wcel
    #
    @6
    cfn
    wcel
    #
    wo
    @3
    @19
    @72
    @71
    @19
    @1
    @72
    @0
    @1
    simpr
    @19
    cI
    @6
    cen
    wbr
    #
    @1
    @72
    wb
    @0
    @68
    @1
    @73
    @69
    cR
    @5
    cI
    cfn
    @42
    uvcendim
    sylan
    #
    cI
    @6
    enfi
    syl
    mpbid
    olcd
    3adant3
    mreexexd
    @14
    @7
    vf
    @15
    @14
    @10
    @9
    @6
    cdom
    wbr
    #
    @7
    @9
    @15
    wcel
    #
    @10
    @13
    simpl
    @6
    cvv
    wcel
    @76
    @9
    @6
    wss
    @75
    @5
    cR
    cI
    cuvc
    ovex
    rnex
    @9
    @6
    elpwi
    @9
    @6
    cvv
    ssdomg
    mpsyl
    cX
    @9
    @6
    endomtr
    syl2anr
    rexlimiva
    syl
    @0
    @1
    @8
    @3
    @19
    cI
    @6
    @74
    ensymd
    3adant3
    cX
    @6
    cI
    domentr
    syl2anc
end
