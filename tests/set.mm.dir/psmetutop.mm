include "c0.mm"
include "wne.mm"
include "cpsmet.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "cmetu.mm"
include "cutop.mm"
include "cbl.mm"
include "crn.mm"
include "ctg.mm"
include "cv.mm"
include "cuni.mm"
include "wss.mm"
include "wrex.mm"
include "wral.mm"
include "cpw.mm"
include "csn.mm"
include "cima.mm"
include "crab.mm"
include "cust.mm"
include "wceq.mm"
include "metuust.mm"
include "utopval.mm"
include "syl.mm"
include "eleq2d.mm"
include "rabid.mm"
include "syl6bb.mm"
include "biimpa.mm"
include "simpld.mm"
include "elpwid.mm"
include "unirnblps.mm"
include "ad2antlr.mm"
include "sseqtr4d.mm"
include "simpr.mm"
include "simp-5r.mm"
include "simplr.mm"
include "ad3antrrr.mm"
include "simpllr.mm"
include "sseldd.mm"
include "metustbl.mm"
include "syl3anc.mm"
include "sstr.mm"
include "expcom.mm"
include "anim2d.mm"
include "reximdv.mm"
include "sylc.mm"
include "simprd.mm"
include "r19.21bi.mm"
include "r19.29a.mm"
include "ralrimiva.mm"
include "jca.mm"
include "cvv.mm"
include "wb.mm"
include "fvex.mm"
include "rnex.mm"
include "eltg2.mm"
include "mp1i.mm"
include "mpbird.mm"
include "sseqtrd.mm"
include "elpwg.mm"
include "adantl.mm"
include "crp.mm"
include "ccnv.mm"
include "cc0.mm"
include "cico.mm"
include "co.mm"
include "cmpt.mm"
include "sselda.mm"
include "blssexps.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "blval2.mm"
include "3expa.mm"
include "sseq1d.mm"
include "rexbidva.mm"
include "syl21anc.mm"
include "cnvexg.mm"
include "imaexg.mm"
include "ralrimivw.mm"
include "eqid.mm"
include "imaeq1.mm"
include "rexrnmpt.mm"
include "3syl.mm"
include "wi.mm"
include "cxp.mm"
include "cfg.mm"
include "cfbas.mm"
include "oveq2.mm"
include "imaeq2d.mm"
include "cbvmptv.mm"
include "rneqi.mm"
include "metustfbas.mm"
include "ssfg.mm"
include "metuval.mm"
include "ssrexv.mm"
include "ad2antrr.mm"
include "mpd.mm"
include "biimpar.mm"
include "syldan.mm"
include "impbida.mm"
include "eqrdv.mm"

theorem psmetutop
  let cD: class D
  let cX: class X
  let va: setvar a
  let vb: setvar b
  let vd: setvar d
  let ve: setvar e
  let vv: setvar v
  let vx: setvar x


  assert |- ( ( X =/= (/) /\ D e. ( PsMet ` X ) ) -> ( unifTop ` ( metUnif ` D ) ) = ( topGen ` ran ( ball ` D ) ) )

  proof
    cX
    c0
    wne
    #
    cD
    cX
    cpsmet
    cfv
    #
    wcel
    #
    wa
    #
    va
    cD
    cmetu
    cfv
    #
    cutop
    cfv
    #
    cD
    cbl
    cfv
    #
    crn
    #
    ctg
    cfv
    #
    @3
    va
    cv
    #
    @5
    wcel
    #
    @9
    @8
    wcel
    #
    @3
    @10
    wa
    #
    @11
    @9
    @7
    cuni
    #
    wss
    #
    vx
    cv
    #
    vb
    cv
    #
    wcel
    #
    @16
    @9
    wss
    #
    wa
    #
    vb
    @7
    wrex
    #
    vx
    @9
    wral
    #
    wa
    #
    @12
    @14
    @21
    @12
    @9
    cX
    @13
    @12
    @9
    cX
    @12
    @9
    cX
    cpw
    #
    wcel
    #
    vv
    cv
    #
    @15
    csn
    #
    cima
    #
    @9
    wss
    #
    vv
    @4
    wrex
    #
    vx
    @9
    wral
    #
    @3
    @10
    @24
    @30
    wa
    #
    @3
    @10
    @9
    @30
    va
    @23
    crab
    #
    wcel
    @31
    @3
    @5
    @32
    @9
    @3
    @4
    cX
    cust
    cfv
    wcel
    @5
    @32
    wceq
    cD
    cX
    metuust
    vx
    vv
    @4
    cX
    va
    utopval
    syl
    eleq2d
    @30
    va
    @23
    rabid
    syl6bb
    #
    biimpa
    #
    simpld
    elpwid
    #
    @2
    @13
    cX
    wceq
    #
    @0
    @10
    cD
    cX
    unirnblps
    #
    ad2antlr
    sseqtr4d
    @12
    @20
    vx
    @9
    @12
    @15
    @9
    wcel
    #
    wa
    #
    @28
    @20
    vv
    @4
    @39
    @25
    @4
    wcel
    #
    wa
    #
    @28
    wa
    #
    @28
    @17
    @16
    @27
    wss
    #
    wa
    #
    vb
    @7
    wrex
    #
    @20
    @41
    @28
    simpr
    @42
    @2
    @40
    @15
    cX
    wcel
    #
    @45
    @0
    @2
    @10
    @38
    @40
    @28
    simp-5r
    @39
    @40
    @28
    simplr
    @42
    @9
    cX
    @15
    @12
    @9
    cX
    wss
    #
    @38
    @40
    @28
    @35
    ad3antrrr
    @12
    @38
    @40
    @28
    simpllr
    sseldd
    cD
    @15
    @25
    cX
    vb
    metustbl
    syl3anc
    @28
    @44
    @19
    vb
    @7
    @28
    @43
    @18
    @17
    @43
    @28
    @18
    @16
    @27
    @9
    sstr
    expcom
    anim2d
    reximdv
    sylc
    @12
    @29
    vx
    @9
    @12
    @24
    @30
    @34
    simprd
    r19.21bi
    r19.29a
    ralrimiva
    jca
    @7
    cvv
    wcel
    #
    @11
    @22
    wb
    #
    @12
    @6
    cD
    cbl
    fvex
    rnex
    #
    vx
    vb
    @9
    @7
    cvv
    eltg2
    #
    mp1i
    mpbird
    @3
    @11
    @31
    @10
    @3
    @11
    wa
    #
    @24
    @30
    @52
    @24
    @47
    @52
    @9
    @13
    cX
    @52
    @14
    @21
    @3
    @11
    @22
    @48
    @49
    @3
    @50
    @51
    mp1i
    biimpa
    #
    simpld
    @2
    @36
    @0
    @11
    @37
    ad2antlr
    sseqtrd
    #
    @11
    @24
    @47
    wb
    @3
    @9
    cX
    @8
    elpwg
    adantl
    mpbird
    @52
    @29
    vx
    @9
    @52
    @38
    wa
    #
    @28
    vv
    vd
    crp
    cD
    ccnv
    #
    cc0
    vd
    cv
    #
    cico
    co
    #
    cima
    #
    cmpt
    #
    crn
    #
    wrex
    #
    @29
    @55
    @62
    @59
    @26
    cima
    #
    @9
    wss
    #
    vd
    crp
    wrex
    #
    @55
    @2
    @46
    @15
    @57
    @6
    co
    #
    @9
    wss
    #
    vd
    crp
    wrex
    #
    @65
    @0
    @2
    @11
    @38
    simpllr
    #
    @52
    @9
    cX
    @15
    @54
    sselda
    #
    @55
    @20
    @68
    @52
    @20
    vx
    @9
    @52
    @14
    @21
    @53
    simprd
    r19.21bi
    @55
    @2
    @46
    @20
    @68
    wb
    @69
    @70
    vb
    @9
    cD
    @15
    cX
    vd
    blssexps
    syl2anc
    mpbid
    @2
    @46
    wa
    #
    @68
    @65
    @71
    @67
    @64
    vd
    crp
    @71
    @57
    crp
    wcel
    #
    wa
    @66
    @63
    @9
    @2
    @46
    @72
    @66
    @63
    wceq
    cD
    @15
    @57
    cX
    blval2
    3expa
    sseq1d
    rexbidva
    biimpa
    syl21anc
    @55
    @2
    @59
    cvv
    wcel
    #
    vd
    crp
    wral
    @62
    @65
    wb
    @69
    @2
    @73
    vd
    crp
    @2
    @56
    cvv
    wcel
    @73
    cD
    @1
    cnvexg
    @56
    @58
    cvv
    imaexg
    syl
    ralrimivw
    @28
    @64
    vd
    vv
    crp
    @59
    @60
    cvv
    @60
    eqid
    @25
    @59
    wceq
    @27
    @63
    @9
    @25
    @59
    @26
    imaeq1
    sseq1d
    rexrnmpt
    3syl
    mpbird
    @3
    @62
    @29
    wi
    #
    @11
    @38
    @3
    @61
    @4
    wss
    @74
    @3
    @61
    cX
    cX
    cxp
    #
    @61
    cfg
    co
    #
    @4
    @3
    @61
    @75
    cfbas
    cfv
    wcel
    @61
    @76
    wss
    cD
    @61
    cX
    ve
    @60
    ve
    crp
    @56
    cc0
    ve
    cv
    #
    cico
    co
    #
    cima
    #
    cmpt
    vd
    ve
    crp
    @59
    @79
    @57
    @77
    wceq
    @58
    @78
    @56
    @57
    @77
    cc0
    cico
    oveq2
    imaeq2d
    cbvmptv
    rneqi
    metustfbas
    @61
    @75
    ssfg
    syl
    @2
    @4
    @76
    wceq
    @0
    cD
    cX
    vd
    metuval
    adantl
    sseqtr4d
    @28
    vv
    @61
    @4
    ssrexv
    syl
    ad2antrr
    mpd
    ralrimiva
    jca
    @3
    @10
    @31
    @33
    biimpar
    syldan
    impbida
    eqrdv
end
