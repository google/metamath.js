include "cxmt.mm"
include "cfv.mm"
include "wcel.mm"
include "wss.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "ccl.mm"
include "wceq.mm"
include "w3a.mm"
include "wa.mm"
include "cn.mm"
include "cv.mm"
include "c1.mm"
include "cdiv.mm"
include "co.mm"
include "cbl.mm"
include "cmpt2.mm"
include "crn.mm"
include "ctg.mm"
include "c2ndc.mm"
include "ctop.mm"
include "wrex.mm"
include "wral.mm"
include "mopntop.mm"
include "adantr.mm"
include "cxp.mm"
include "wf.mm"
include "cxr.mm"
include "simpll.mm"
include "simplr1.mm"
include "simprr.mm"
include "sseldd.mm"
include "simprl.mm"
include "nnrpd.mm"
include "rpreccld.mm"
include "rpxrd.mm"
include "blopn.mm"
include "syl3anc.mm"
include "ralrimivva.mm"
include "eqid.mm"
include "fmpt2.mm"
include "sylib.mm"
include "frn.mm"
include "syl.mm"
include "crp.mm"
include "mopni2.mm"
include "c2.mm"
include "clt.mm"
include "rphalfcld.mm"
include "cr.mm"
include "cc0.mm"
include "elrp.mm"
include "nnrecl.mm"
include "sylbi.mm"
include "cin.mm"
include "c0.mm"
include "wne.mm"
include "wex.mm"
include "cuni.mm"
include "ad2antrr.mm"
include "simpr1.mm"
include "mopnuni.mm"
include "ad3antrrr.mm"
include "sseqtrd.mm"
include "simplrr.mm"
include "simplrl.mm"
include "elunii.mm"
include "syl2anc.mm"
include "eleqtrrd.mm"
include "simpr3.mm"
include "simprrl.mm"
include "blcntr.mm"
include "clsndisj.mm"
include "syl32anc.mm"
include "n0.mm"
include "inss2.mm"
include "simpr.mm"
include "sseldi.mm"
include "eqidd.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "eqeq2d.mm"
include "oveq1.mm"
include "rspc2ev.mm"
include "ovex.mm"
include "eqeq1.mm"
include "2rexbidv.mm"
include "rnmpt2.mm"
include "elab2.mm"
include "sylibr.mm"
include "inss1.mm"
include "wb.mm"
include "blcom.mm"
include "syl22anc.mm"
include "mpbid.mm"
include "cle.mm"
include "simprll.mm"
include "simprrr.mm"
include "wi.mm"
include "rpre.mm"
include "ltle.mm"
include "syl2an.mm"
include "mpd.mm"
include "ssbl.mm"
include "syl221anc.mm"
include "rpred.mm"
include "blhalf.mm"
include "simprlr.mm"
include "sstrd.mm"
include "eleq2.mm"
include "sseq1.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "syl12anc.mm"
include "exlimddv.mm"
include "anassrs.mm"
include "rexlimddv.mm"
include "basgen2.mm"
include "ctb.mm"
include "eqeltrd.mm"
include "tgclb.mm"
include "ccrd.mm"
include "cdm.mm"
include "wfo.mm"
include "con0.mm"
include "omelon.mm"
include "cen.mm"
include "simpr2.mm"
include "nnex.mm"
include "xpdom2.mm"
include "nnenom.mm"
include "omex.mm"
include "enref.mm"
include "xpen.mm"
include "mp2an.mm"
include "xpomen.mm"
include "entri.mm"
include "domentr.mm"
include "sylancl.mm"
include "ondomen.mm"
include "sylancr.mm"
include "wfn.mm"
include "ffn.mm"
include "dffn4.mm"
include "fodomnum.mm"
include "sylc.mm"
include "domtr.mm"
include "2ndci.mm"
include "eqeltrrd.mm"

theorem met2ndci
  let cA: class A
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
  assume methaus.1: |- J = ( MetOpen ` D )


  assert |- ( ( D e. ( *Met ` X ) /\ ( A C_ X /\ A ~<_ _om /\ ( ( cls ` J ) ` A ) = X ) ) -> J e. 2ndc )

  proof
    cD
    cX
    cxmt
    cfv
    wcel
    #
    cA
    cX
    wss
    #
    cA
    com
    cdom
    wbr
    #
    cA
    cJ
    ccl
    cfv
    cfv
    #
    cX
    wceq
    #
    w3a
    #
    wa
    #
    vx
    vy
    cn
    cA
    vy
    cv
    #
    c1
    vx
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
    cmpt2
    #
    crn
    #
    ctg
    cfv
    #
    cJ
    c2ndc
    @6
    cJ
    ctop
    wcel
    #
    @13
    cJ
    wss
    #
    vz
    cv
    #
    vw
    cv
    #
    wcel
    #
    @18
    vu
    cv
    #
    wss
    #
    wa
    #
    vw
    @13
    wrex
    #
    vz
    @20
    wral
    vu
    cJ
    wral
    @14
    cJ
    wceq
    @0
    @15
    @5
    cD
    cJ
    cX
    methaus.1
    mopntop
    adantr
    #
    @6
    cn
    cA
    cxp
    #
    cJ
    @12
    wf
    #
    @16
    @6
    @11
    cJ
    wcel
    #
    vy
    cA
    wral
    vx
    cn
    wral
    @26
    @6
    @27
    vx
    vy
    cn
    cA
    @6
    @8
    cn
    wcel
    #
    @7
    cA
    wcel
    #
    wa
    #
    wa
    #
    @0
    @7
    cX
    wcel
    @9
    cxr
    wcel
    @27
    @0
    @5
    @30
    simpll
    @31
    cA
    cX
    @7
    @1
    @2
    @4
    @0
    @30
    simplr1
    @6
    @28
    @29
    simprr
    sseldd
    @31
    @9
    @31
    @8
    @31
    @8
    @6
    @28
    @29
    simprl
    nnrpd
    rpreccld
    rpxrd
    cD
    @7
    @9
    cJ
    cX
    methaus.1
    blopn
    syl3anc
    ralrimivva
    vx
    vy
    cn
    cA
    @11
    cJ
    @12
    @12
    eqid
    #
    fmpt2
    sylib
    #
    @25
    cJ
    @12
    frn
    syl
    @6
    @23
    vu
    vz
    cJ
    @20
    @6
    @20
    cJ
    wcel
    #
    @17
    @20
    wcel
    #
    wa
    #
    wa
    #
    @17
    vr
    cv
    #
    @10
    co
    #
    @20
    wss
    #
    @23
    vr
    crp
    @37
    @0
    @34
    @35
    @40
    vr
    crp
    wrex
    @0
    @5
    @36
    simpll
    #
    @6
    @34
    @35
    simprl
    @6
    @34
    @35
    simprr
    vr
    @20
    cD
    @17
    cJ
    cX
    methaus.1
    mopni2
    syl3anc
    @37
    @38
    crp
    wcel
    #
    @40
    wa
    #
    wa
    #
    c1
    vn
    cv
    #
    cdiv
    co
    #
    @38
    c2
    cdiv
    co
    #
    clt
    wbr
    #
    @23
    vn
    cn
    @44
    @47
    crp
    wcel
    #
    @48
    vn
    cn
    wrex
    #
    @44
    @38
    @37
    @42
    @40
    simprl
    rphalfcld
    @49
    @47
    cr
    wcel
    #
    cc0
    @47
    clt
    wbr
    wa
    @50
    @47
    elrp
    @47
    vn
    nnrecl
    sylbi
    syl
    @37
    @43
    @45
    cn
    wcel
    #
    @48
    wa
    #
    @23
    @37
    @43
    @53
    wa
    #
    wa
    #
    vt
    cv
    #
    @17
    @46
    @10
    co
    #
    cA
    cin
    #
    wcel
    #
    @23
    vt
    @55
    @58
    c0
    wne
    #
    @59
    vt
    wex
    @55
    @15
    cA
    cJ
    cuni
    #
    wss
    @17
    @3
    wcel
    @57
    cJ
    wcel
    #
    @17
    @57
    wcel
    #
    @60
    @6
    @15
    @36
    @54
    @24
    ad2antrr
    @55
    cA
    cX
    @61
    @6
    @1
    @36
    @54
    @0
    @1
    @2
    @4
    simpr1
    ad2antrr
    #
    @0
    cX
    @61
    wceq
    @5
    @36
    @54
    cD
    cJ
    cX
    methaus.1
    mopnuni
    ad3antrrr
    #
    sseqtrd
    @55
    @17
    cX
    @3
    @55
    @17
    @61
    cX
    @55
    @35
    @34
    @17
    @61
    wcel
    @6
    @34
    @35
    @54
    simplrr
    @6
    @34
    @35
    @54
    simplrl
    @17
    @20
    cJ
    elunii
    syl2anc
    @65
    eleqtrrd
    #
    @6
    @4
    @36
    @54
    @0
    @1
    @2
    @4
    simpr3
    ad2antrr
    eleqtrrd
    @55
    @0
    @17
    cX
    wcel
    #
    @46
    cxr
    wcel
    #
    @62
    @37
    @0
    @54
    @41
    adantr
    #
    @66
    @55
    @46
    @55
    @45
    @55
    @45
    @37
    @43
    @52
    @48
    simprrl
    #
    nnrpd
    rpreccld
    #
    rpxrd
    #
    cD
    @17
    @46
    cJ
    cX
    methaus.1
    blopn
    syl3anc
    @55
    @0
    @67
    @46
    crp
    wcel
    #
    @63
    @69
    @66
    @71
    cD
    @17
    @46
    cX
    blcntr
    syl3anc
    @17
    cA
    @57
    cJ
    @61
    @61
    eqid
    clsndisj
    syl32anc
    vt
    @58
    n0
    sylib
    @55
    @59
    wa
    #
    @56
    @46
    @10
    co
    #
    @13
    wcel
    #
    @17
    @75
    wcel
    #
    @75
    @20
    wss
    #
    @23
    @74
    @75
    @11
    wceq
    #
    vy
    cA
    wrex
    vx
    cn
    wrex
    #
    @76
    @74
    @52
    @56
    cA
    wcel
    @75
    @75
    wceq
    #
    @80
    @55
    @52
    @59
    @70
    adantr
    @74
    @58
    cA
    @56
    @57
    cA
    inss2
    @55
    @59
    simpr
    #
    sseldi
    #
    @74
    @75
    eqidd
    @79
    @81
    @75
    @7
    @46
    @10
    co
    #
    wceq
    vx
    vy
    @45
    @56
    cn
    cA
    @8
    @45
    wceq
    #
    @11
    @84
    @75
    @85
    @9
    @46
    @7
    @10
    @8
    @45
    c1
    cdiv
    oveq2
    oveq2d
    eqeq2d
    @7
    @56
    wceq
    @84
    @75
    @75
    @7
    @56
    @46
    @10
    oveq1
    eqeq2d
    rspc2ev
    syl3anc
    @17
    @11
    wceq
    #
    vy
    cA
    wrex
    vx
    cn
    wrex
    @80
    vz
    @75
    @13
    @56
    @46
    @10
    ovex
    @17
    @75
    wceq
    @86
    @79
    vx
    vy
    cn
    cA
    @17
    @75
    @11
    eqeq1
    2rexbidv
    vx
    vy
    vz
    cn
    cA
    @11
    @12
    @32
    rnmpt2
    elab2
    sylibr
    @74
    @56
    @57
    wcel
    #
    @77
    @74
    @58
    @57
    @56
    @57
    cA
    inss1
    @82
    sseldi
    @74
    @0
    @68
    @67
    @56
    cX
    wcel
    #
    @87
    @77
    wb
    @55
    @0
    @59
    @69
    adantr
    #
    @55
    @68
    @59
    @72
    adantr
    #
    @55
    @67
    @59
    @66
    adantr
    @74
    cA
    cX
    @56
    @55
    @1
    @59
    @64
    adantr
    @83
    sseldd
    #
    @56
    cD
    @17
    @46
    cX
    blcom
    syl22anc
    mpbid
    #
    @74
    @75
    @56
    @47
    @10
    co
    #
    @20
    @74
    @0
    @88
    @68
    @47
    cxr
    wcel
    @46
    @47
    cle
    wbr
    #
    @75
    @93
    wss
    @89
    @91
    @90
    @74
    @47
    @74
    @38
    @55
    @42
    @59
    @37
    @42
    @40
    @53
    simprll
    #
    adantr
    #
    rphalfcld
    rpxrd
    @55
    @94
    @59
    @55
    @48
    @94
    @37
    @43
    @52
    @48
    simprrr
    @55
    @73
    @49
    @48
    @94
    wi
    #
    @71
    @55
    @38
    @95
    rphalfcld
    @73
    @46
    cr
    wcel
    @51
    @97
    @49
    @46
    rpre
    @47
    rpre
    @46
    @47
    ltle
    syl2an
    syl2anc
    mpd
    adantr
    cD
    @56
    @46
    @47
    cX
    ssbl
    syl221anc
    #
    @74
    @93
    @39
    @20
    @74
    @0
    @88
    @38
    cr
    wcel
    @17
    @93
    wcel
    @93
    @39
    wss
    @89
    @91
    @74
    @38
    @96
    rpred
    @74
    @75
    @93
    @17
    @98
    @92
    sseldd
    @38
    cD
    cX
    @56
    @17
    blhalf
    syl22anc
    @55
    @40
    @59
    @37
    @42
    @40
    @53
    simprlr
    adantr
    sstrd
    sstrd
    @22
    @77
    @78
    wa
    vw
    @75
    @13
    @18
    @75
    wceq
    @19
    @77
    @21
    @78
    @18
    @75
    @17
    eleq2
    @18
    @75
    @20
    sseq1
    anbi12d
    rspcev
    syl12anc
    exlimddv
    anassrs
    rexlimddv
    rexlimddv
    ralrimivva
    vu
    vz
    vw
    @13
    cJ
    basgen2
    syl3anc
    #
    @6
    @13
    ctb
    wcel
    #
    @13
    com
    cdom
    wbr
    #
    @14
    c2ndc
    wcel
    @6
    @14
    ctop
    wcel
    @100
    @6
    @14
    cJ
    ctop
    @99
    @24
    eqeltrd
    @13
    tgclb
    sylibr
    @6
    @13
    @25
    cdom
    wbr
    #
    @25
    com
    cdom
    wbr
    #
    @101
    @6
    @25
    ccrd
    cdm
    wcel
    #
    @25
    @13
    @12
    wfo
    #
    @102
    @6
    com
    con0
    wcel
    @103
    @104
    omelon
    @6
    @25
    cn
    com
    cxp
    #
    cdom
    wbr
    #
    @106
    com
    cen
    wbr
    @103
    @6
    @2
    @107
    @0
    @1
    @2
    @4
    simpr2
    cA
    com
    cn
    nnex
    xpdom2
    syl
    @106
    com
    com
    cxp
    #
    com
    cn
    com
    cen
    wbr
    com
    com
    cen
    wbr
    @106
    @108
    cen
    wbr
    nnenom
    com
    omex
    enref
    cn
    com
    com
    com
    xpen
    mp2an
    xpomen
    entri
    @25
    @106
    com
    domentr
    sylancl
    #
    com
    @25
    ondomen
    sylancr
    @6
    @12
    @25
    wfn
    #
    @105
    @6
    @26
    @110
    @33
    @25
    cJ
    @12
    ffn
    syl
    @25
    @12
    dffn4
    sylib
    @25
    @13
    @12
    fodomnum
    sylc
    @109
    @13
    @25
    com
    domtr
    syl2anc
    @13
    2ndci
    syl2anc
    eqeltrrd
end
