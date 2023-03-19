include "cxmt.mm"
include "cfv.mm"
include "wcel.mm"
include "ctop.mm"
include "cv.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "wel.mm"
include "wss.mm"
include "wa.mm"
include "wrex.mm"
include "wi.mm"
include "wral.mm"
include "cpw.mm"
include "cuni.mm"
include "c1stc.mm"
include "mopntop.mm"
include "mopnuni.mm"
include "eleq2d.mm"
include "biimpar.mm"
include "cn.mm"
include "c1.mm"
include "cdiv.mm"
include "co.mm"
include "cbl.mm"
include "cmpt.mm"
include "crn.mm"
include "wf.mm"
include "cxr.mm"
include "simpll.mm"
include "simplr.mm"
include "crp.mm"
include "nnrp.mm"
include "adantl.mm"
include "rpreccld.mm"
include "rpxrd.mm"
include "blopn.mm"
include "syl3anc.mm"
include "eqid.mm"
include "fmptd.mm"
include "frn.mm"
include "syl.mm"
include "nnex.mm"
include "mptex.mm"
include "rnex.mm"
include "elpw.mm"
include "sylibr.mm"
include "cen.mm"
include "ccrd.mm"
include "cdm.mm"
include "wfo.mm"
include "con0.mm"
include "omelon.mm"
include "nnenom.mm"
include "ensymi.mm"
include "isnumi.mm"
include "mp2an.mm"
include "wfn.mm"
include "ovex.mm"
include "fnmpti.mm"
include "dffn4.mm"
include "mpbi.mm"
include "fodomnum.mm"
include "mp2.mm"
include "domentr.mm"
include "a1i.mm"
include "simprl.mm"
include "simprr.mm"
include "mopni2.mm"
include "clt.mm"
include "simp-4l.mm"
include "simp-4r.mm"
include "nnrpd.mm"
include "blcntr.mm"
include "cle.mm"
include "simplrl.mm"
include "cr.mm"
include "nnrecre.mm"
include "ad2antrl.mm"
include "rpred.mm"
include "ltled.mm"
include "ssbl.mm"
include "syl221anc.mm"
include "simplrr.mm"
include "sstrd.mm"
include "jca.mm"
include "cc0.mm"
include "elrp.mm"
include "nnrecl.mm"
include "sylbi.mm"
include "reximddv.mm"
include "rexlimddv.mm"
include "cvv.mm"
include "ovexd.mm"
include "wceq.mm"
include "wb.mm"
include "vex.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "cbvmptv.mm"
include "elrnmpt.mm"
include "mp1i.mm"
include "eleq2.mm"
include "sseq1.mm"
include "anbi12d.mm"
include "rexxfr2d.mm"
include "mpbird.mm"
include "expr.mm"
include "ralrimiva.mm"
include "breq1.mm"
include "rexeq.mm"
include "imbi2d.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "syl12anc.mm"
include "syldan.mm"
include "is1stc2.mm"
include "sylanbrc.mm"

theorem met1stc
  let cD: class D
  let cJ: class J
  let cX: class X
  let vd: setvar d
  let vn: setvar n
  let vr: setvar r
  let vt: setvar t
  let vu: setvar u
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vm: setvar m
  let cA: class A
  assume methaus.1: |- J = ( MetOpen ` D )


  assert |- ( D e. ( *Met ` X ) -> J e. 1stc )

  proof
    cD
    cX
    cxmt
    cfv
    wcel
    #
    cJ
    ctop
    wcel
    vy
    cv
    #
    com
    cdom
    wbr
    #
    vx
    vz
    wel
    #
    vx
    vw
    wel
    #
    vw
    cv
    #
    vz
    cv
    #
    wss
    #
    wa
    #
    vw
    @1
    wrex
    #
    wi
    #
    vz
    cJ
    wral
    #
    wa
    #
    vy
    cJ
    cpw
    #
    wrex
    #
    vx
    cJ
    cuni
    #
    wral
    cJ
    c1stc
    wcel
    cD
    cJ
    cX
    methaus.1
    mopntop
    @0
    @14
    vx
    @15
    @0
    vx
    cv
    #
    @15
    wcel
    #
    @16
    cX
    wcel
    #
    @14
    @0
    @18
    @17
    @0
    cX
    @15
    @16
    cD
    cJ
    cX
    methaus.1
    mopnuni
    eleq2d
    biimpar
    @0
    @18
    wa
    #
    vn
    cn
    @16
    c1
    vn
    cv
    #
    cdiv
    co
    #
    cD
    cbl
    cfv
    #
    co
    #
    cmpt
    #
    crn
    #
    @13
    wcel
    #
    @25
    com
    cdom
    wbr
    #
    @3
    @8
    vw
    @25
    wrex
    #
    wi
    #
    vz
    cJ
    wral
    #
    @14
    @19
    @25
    cJ
    wss
    #
    @26
    @19
    cn
    cJ
    @24
    wf
    @31
    @19
    vn
    cn
    @23
    cJ
    @24
    @19
    @20
    cn
    wcel
    #
    wa
    #
    @0
    @18
    @21
    cxr
    wcel
    @23
    cJ
    wcel
    @0
    @18
    @32
    simpll
    @0
    @18
    @32
    simplr
    @33
    @21
    @33
    @20
    @32
    @20
    crp
    wcel
    @19
    @20
    nnrp
    adantl
    rpreccld
    rpxrd
    cD
    @16
    @21
    cJ
    cX
    methaus.1
    blopn
    syl3anc
    @24
    eqid
    #
    fmptd
    cn
    cJ
    @24
    frn
    syl
    @25
    cJ
    @24
    vn
    cn
    @23
    nnex
    mptex
    rnex
    elpw
    sylibr
    @27
    @19
    @25
    cn
    cdom
    wbr
    #
    cn
    com
    cen
    wbr
    @27
    cn
    ccrd
    cdm
    wcel
    #
    cn
    @25
    @24
    wfo
    #
    @35
    com
    con0
    wcel
    com
    cn
    cen
    wbr
    @36
    omelon
    cn
    com
    nnenom
    ensymi
    com
    cn
    isnumi
    mp2an
    @24
    cn
    wfn
    @37
    vn
    cn
    @23
    @24
    @16
    @21
    @22
    ovex
    @34
    fnmpti
    cn
    @24
    dffn4
    mpbi
    cn
    @25
    @24
    fodomnum
    mp2
    nnenom
    @25
    cn
    com
    domentr
    mp2an
    a1i
    @19
    @29
    vz
    cJ
    @19
    @6
    cJ
    wcel
    #
    @3
    @28
    @19
    @38
    @3
    wa
    #
    wa
    #
    @28
    @16
    @16
    c1
    @1
    cdiv
    co
    #
    @22
    co
    #
    wcel
    #
    @42
    @6
    wss
    #
    wa
    #
    vy
    cn
    wrex
    #
    @40
    @16
    vr
    cv
    #
    @22
    co
    #
    @6
    wss
    #
    @46
    vr
    crp
    @40
    @0
    @38
    @3
    @49
    vr
    crp
    wrex
    @0
    @18
    @39
    simpll
    @19
    @38
    @3
    simprl
    @19
    @38
    @3
    simprr
    vr
    @6
    cD
    @16
    cJ
    cX
    methaus.1
    mopni2
    syl3anc
    @40
    @47
    crp
    wcel
    #
    @49
    wa
    #
    wa
    #
    @41
    @47
    clt
    wbr
    #
    @45
    vy
    cn
    @52
    @1
    cn
    wcel
    #
    @53
    wa
    #
    wa
    #
    @43
    @44
    @56
    @0
    @18
    @41
    crp
    wcel
    @43
    @0
    @18
    @39
    @51
    @55
    simp-4l
    #
    @0
    @18
    @39
    @51
    @55
    simp-4r
    #
    @56
    @1
    @56
    @1
    @52
    @54
    @53
    simprl
    nnrpd
    rpreccld
    #
    cD
    @16
    @41
    cX
    blcntr
    syl3anc
    @56
    @42
    @48
    @6
    @56
    @0
    @18
    @41
    cxr
    wcel
    @47
    cxr
    wcel
    @41
    @47
    cle
    wbr
    @42
    @48
    wss
    @57
    @58
    @56
    @41
    @59
    rpxrd
    @56
    @47
    @40
    @50
    @49
    @55
    simplrl
    #
    rpxrd
    @56
    @41
    @47
    @54
    @41
    cr
    wcel
    @52
    @53
    @1
    nnrecre
    ad2antrl
    @56
    @47
    @60
    rpred
    @52
    @54
    @53
    simprr
    ltled
    cD
    @16
    @41
    @47
    cX
    ssbl
    syl221anc
    @40
    @50
    @49
    @55
    simplrr
    sstrd
    jca
    @50
    @53
    vy
    cn
    wrex
    #
    @40
    @49
    @50
    @47
    cr
    wcel
    cc0
    @47
    clt
    wbr
    wa
    @61
    @47
    elrp
    @47
    vy
    nnrecl
    sylbi
    ad2antrl
    reximddv
    rexlimddv
    @40
    @8
    @45
    vw
    vy
    @42
    @25
    cn
    cvv
    @40
    @54
    wa
    @16
    @41
    @22
    ovexd
    @5
    cvv
    wcel
    @5
    @25
    wcel
    @5
    @42
    wceq
    #
    vy
    cn
    wrex
    wb
    @40
    vw
    vex
    vy
    cn
    @42
    @5
    @24
    cvv
    vn
    vy
    cn
    @23
    @42
    @20
    @1
    wceq
    @21
    @41
    @16
    @22
    @20
    @1
    c1
    cdiv
    oveq2
    oveq2d
    cbvmptv
    elrnmpt
    mp1i
    @62
    @8
    @45
    wb
    @40
    @62
    @4
    @43
    @7
    @44
    @5
    @42
    @16
    eleq2
    @5
    @42
    @6
    sseq1
    anbi12d
    adantl
    rexxfr2d
    mpbird
    expr
    ralrimiva
    @12
    @27
    @30
    wa
    vy
    @25
    @13
    @1
    @25
    wceq
    #
    @2
    @27
    @11
    @30
    @1
    @25
    com
    cdom
    breq1
    @63
    @10
    @29
    vz
    cJ
    @63
    @9
    @28
    @3
    @8
    vw
    @1
    @25
    rexeq
    imbi2d
    ralbidv
    anbi12d
    rspcev
    syl12anc
    syldan
    ralrimiva
    vx
    vy
    vz
    vw
    cJ
    @15
    @15
    eqid
    is1stc2
    sylanbrc
end
