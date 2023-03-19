include "cpsmet.mm"
include "cfv.mm"
include "wcel.mm"
include "cpstm.mm"
include "cqs.mm"
include "cxmt.mm"
include "cxp.mm"
include "cxr.mm"
include "wf.mm"
include "cv.mm"
include "co.mm"
include "cc0.mm"
include "wceq.mm"
include "wb.mm"
include "cxad.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "wa.mm"
include "wfn.mm"
include "wrex.mm"
include "cab.mm"
include "cuni.mm"
include "cmpt2.mm"
include "eqid.mm"
include "vex.mm"
include "ab2rexex.mm"
include "uniex.mm"
include "fnmpt2i.mm"
include "pstmval.mm"
include "fneq1d.mm"
include "mpbiri.mm"
include "cec.mm"
include "simpllr.mm"
include "simpr.mm"
include "oveq12d.mm"
include "simp-5l.mm"
include "simp-4r.mm"
include "simplr.mm"
include "pstmfval.mm"
include "syl3anc.mm"
include "eqtrd.mm"
include "psmetf.mm"
include "syl.mm"
include "fovrnd.mm"
include "eqeltrd.mm"
include "elqsi.mm"
include "ad2antll.mm"
include "ad2antrr.mm"
include "r19.29a.mm"
include "ad2antrl.mm"
include "ralrimivva.mm"
include "ffnov.mm"
include "sylanbrc.mm"
include "3expa.mm"
include "eqeq1d.mm"
include "cmetid.mm"
include "breqi.mm"
include "metidv.mm"
include "anassrs.mm"
include "syl5bb.mm"
include "wer.mm"
include "metider.mm"
include "ereq1.mm"
include "ax-mp.mm"
include "sylibr.mm"
include "erth.mm"
include "3bitr2d.mm"
include "adantllr.mm"
include "adantlr.mm"
include "adantr.mm"
include "eqeq12d.mm"
include "3bitr4d.mm"
include "simp-6l.mm"
include "simp-6r.mm"
include "psmettri2.mm"
include "syl13anc.mm"
include "simp-5r.mm"
include "3brtr4d.mm"
include "adantl6r.mm"
include "ad5antlr.mm"
include "adantl5r.mm"
include "ad4antlr.mm"
include "adantl4r.mm"
include "ad3antlr.mm"
include "ralrimiva.mm"
include "anasss.mm"
include "jca.mm"
include "cvv.mm"
include "elfvex.mm"
include "qsexg.mm"
include "isxmet.mm"
include "3syl.mm"
include "mpbir2and.mm"

theorem pstmxmet
  let cD: class D
  let c.sm: class .~
  let cX: class X
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let ve: setvar e
  let vf: setvar f
  let cA: class A
  let cB: class B
  assume pstmval.1: |- .~ = ( ~Met ` D )


  assert |- ( D e. ( PsMet ` X ) -> ( pstoMet ` D ) e. ( *Met ` ( X /. .~ ) ) )

  proof
    cD
    cX
    cpsmet
    cfv
    wcel
    #
    cD
    cpstm
    cfv
    #
    cX
    c.sm
    cqs
    #
    cxmt
    cfv
    wcel
    #
    @2
    @2
    cxp
    #
    cxr
    @1
    wf
    #
    vx
    cv
    #
    vy
    cv
    #
    @1
    co
    #
    cc0
    wceq
    #
    @6
    @7
    wceq
    #
    wb
    #
    @8
    vz
    cv
    #
    @6
    @1
    co
    #
    @12
    @7
    @1
    co
    #
    cxad
    co
    #
    cle
    wbr
    #
    vz
    @2
    wral
    #
    wa
    #
    vy
    @2
    wral
    vx
    @2
    wral
    #
    @0
    @1
    @4
    wfn
    #
    @8
    cxr
    wcel
    #
    vy
    @2
    wral
    vx
    @2
    wral
    @5
    @0
    @20
    vx
    vy
    @2
    @2
    @12
    va
    cv
    #
    vb
    cv
    #
    cD
    co
    #
    wceq
    vb
    @7
    wrex
    va
    @6
    wrex
    vz
    cab
    #
    cuni
    #
    cmpt2
    #
    @4
    wfn
    vx
    vy
    @2
    @2
    @26
    @27
    @27
    eqid
    @25
    va
    vb
    vz
    @6
    @7
    @24
    vx
    vex
    vy
    vex
    ab2rexex
    uniex
    fnmpt2i
    @0
    @4
    @1
    @27
    va
    vb
    vz
    cD
    c.sm
    cX
    vx
    vy
    pstmval.1
    pstmval
    fneq1d
    mpbiri
    @0
    @21
    vx
    vy
    @2
    @2
    @0
    @6
    @2
    wcel
    #
    @7
    @2
    wcel
    #
    wa
    #
    wa
    #
    @6
    @22
    c.sm
    cec
    #
    wceq
    #
    @21
    va
    cX
    @31
    @22
    cX
    wcel
    #
    wa
    #
    @33
    wa
    #
    @7
    @23
    c.sm
    cec
    #
    wceq
    #
    @21
    vb
    cX
    @36
    @23
    cX
    wcel
    #
    wa
    #
    @38
    wa
    #
    @8
    @24
    cxr
    @41
    @8
    @32
    @37
    @1
    co
    #
    @24
    @41
    @6
    @32
    @7
    @37
    @1
    @35
    @33
    @39
    @38
    simpllr
    #
    @40
    @38
    simpr
    #
    oveq12d
    #
    @41
    @0
    @34
    @39
    @42
    @24
    wceq
    #
    @0
    @30
    @34
    @33
    @39
    @38
    simp-5l
    #
    @31
    @34
    @33
    @39
    @38
    simp-4r
    #
    @36
    @39
    @38
    simplr
    #
    @22
    @23
    cD
    c.sm
    cX
    pstmval.1
    pstmfval
    #
    syl3anc
    eqtrd
    @41
    @22
    @23
    cxr
    cX
    cX
    cD
    @41
    @0
    cX
    cX
    cxp
    cxr
    cD
    wf
    @47
    cD
    cX
    psmetf
    syl
    @48
    @49
    fovrnd
    eqeltrd
    @31
    @38
    vb
    cX
    wrex
    #
    @34
    @33
    @29
    @51
    @0
    @28
    vb
    cX
    @7
    c.sm
    elqsi
    #
    ad2antll
    ad2antrr
    #
    r19.29a
    @28
    @33
    va
    cX
    wrex
    #
    @0
    @29
    va
    cX
    @6
    c.sm
    elqsi
    #
    ad2antrl
    #
    r19.29a
    ralrimivva
    vx
    vy
    @2
    @2
    cxr
    @1
    ffnov
    sylanbrc
    @0
    @18
    vx
    vy
    @2
    @2
    @31
    @11
    @17
    @31
    @33
    @11
    va
    cX
    @36
    @38
    @11
    vb
    cX
    @41
    @42
    cc0
    wceq
    #
    @32
    @37
    wceq
    #
    @9
    @10
    @40
    @57
    @58
    wb
    #
    @38
    @35
    @39
    @59
    @33
    @0
    @34
    @39
    @59
    @30
    @0
    @34
    wa
    #
    @39
    wa
    #
    @57
    @24
    cc0
    wceq
    #
    @22
    @23
    c.sm
    wbr
    #
    @58
    @61
    @42
    @24
    cc0
    @0
    @34
    @39
    @46
    @50
    3expa
    eqeq1d
    @63
    @22
    @23
    cD
    cmetid
    cfv
    #
    wbr
    #
    @61
    @62
    @22
    @23
    c.sm
    @64
    pstmval.1
    breqi
    @0
    @34
    @39
    @65
    @62
    wb
    @22
    @23
    cD
    cX
    metidv
    anassrs
    syl5bb
    @61
    @22
    @23
    c.sm
    cX
    @61
    cX
    @64
    wer
    #
    cX
    c.sm
    wer
    #
    @0
    @66
    @34
    @39
    cD
    cX
    metider
    ad2antrr
    c.sm
    @64
    wceq
    @67
    @66
    wb
    pstmval.1
    cX
    c.sm
    @64
    ereq1
    ax-mp
    sylibr
    @0
    @34
    @39
    simplr
    erth
    3bitr2d
    adantllr
    adantlr
    adantr
    @41
    @8
    @42
    cc0
    @45
    eqeq1d
    @41
    @6
    @32
    @7
    @37
    @43
    @44
    eqeq12d
    3bitr4d
    @53
    r19.29a
    @56
    r19.29a
    @0
    @28
    @29
    @17
    @0
    @28
    wa
    @29
    wa
    #
    @16
    vz
    @2
    @68
    @12
    @2
    wcel
    #
    wa
    @33
    @16
    va
    cX
    @0
    @28
    @29
    @69
    @34
    @33
    @16
    @0
    @29
    wa
    @69
    wa
    @34
    wa
    @33
    wa
    @38
    @16
    vb
    cX
    @0
    @29
    @69
    @34
    @33
    @39
    @38
    @16
    @0
    @69
    wa
    @34
    wa
    @33
    wa
    @39
    wa
    @38
    wa
    @12
    vc
    cv
    #
    c.sm
    cec
    #
    wceq
    #
    @16
    vc
    cX
    @0
    @69
    @34
    @33
    @39
    @38
    @70
    cX
    wcel
    #
    @72
    @16
    @60
    @33
    wa
    #
    @39
    wa
    #
    @38
    wa
    #
    @73
    wa
    #
    @72
    wa
    #
    @24
    @70
    @22
    cD
    co
    #
    @70
    @23
    cD
    co
    #
    cxad
    co
    #
    @8
    @15
    cle
    @78
    @0
    @73
    @34
    @39
    @24
    @81
    cle
    wbr
    @0
    @34
    @33
    @39
    @38
    @73
    @72
    simp-6l
    #
    @76
    @73
    @72
    simplr
    #
    @0
    @34
    @33
    @39
    @38
    @73
    @72
    simp-6r
    #
    @74
    @39
    @38
    @73
    @72
    simp-4r
    #
    @22
    @23
    @70
    cD
    cX
    psmettri2
    syl13anc
    @78
    @8
    @42
    @24
    @78
    @6
    @32
    @7
    @37
    @1
    @60
    @33
    @39
    @38
    @73
    @72
    simp-5r
    #
    @75
    @38
    @73
    @72
    simpllr
    #
    oveq12d
    @78
    @0
    @34
    @39
    @46
    @82
    @84
    @85
    @50
    syl3anc
    eqtrd
    @78
    @13
    @79
    @14
    @80
    cxad
    @78
    @13
    @71
    @32
    @1
    co
    #
    @79
    @78
    @12
    @71
    @6
    @32
    @1
    @77
    @72
    simpr
    #
    @86
    oveq12d
    @78
    @0
    @73
    @34
    @88
    @79
    wceq
    @82
    @83
    @84
    @70
    @22
    cD
    c.sm
    cX
    pstmval.1
    pstmfval
    syl3anc
    eqtrd
    @78
    @14
    @71
    @37
    @1
    co
    #
    @80
    @78
    @12
    @71
    @7
    @37
    @1
    @89
    @87
    oveq12d
    @78
    @0
    @73
    @39
    @90
    @80
    wceq
    @82
    @83
    @85
    @70
    @23
    cD
    c.sm
    cX
    pstmval.1
    pstmfval
    syl3anc
    eqtrd
    oveq12d
    3brtr4d
    adantl6r
    @69
    @72
    vc
    cX
    wrex
    @0
    @34
    @33
    @39
    @38
    vc
    cX
    @12
    c.sm
    elqsi
    ad5antlr
    r19.29a
    adantl5r
    @29
    @51
    @0
    @69
    @34
    @33
    @52
    ad4antlr
    r19.29a
    adantl4r
    @28
    @54
    @0
    @29
    @69
    @55
    ad3antlr
    r19.29a
    ralrimiva
    anasss
    jca
    ralrimivva
    @0
    cX
    cvv
    wcel
    @2
    cvv
    wcel
    @3
    @5
    @19
    wa
    wb
    cD
    cX
    cpsmet
    elfvex
    cX
    c.sm
    cvv
    qsexg
    vx
    vy
    vz
    cvv
    @1
    @2
    isxmet
    3syl
    mpbir2and
end
