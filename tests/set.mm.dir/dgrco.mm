include "cc.mm"
include "cply.mm"
include "cfv.mm"
include "wcel.mm"
include "cv.mm"
include "cdgr.mm"
include "cle.mm"
include "wbr.mm"
include "ccom.mm"
include "cmul.mm"
include "co.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "plyssc.mm"
include "sseldi.mm"
include "cn0.mm"
include "dgrcl.mm"
include "syl.mm"
include "syl5eqel.mm"
include "cc0.mm"
include "c1.mm"
include "caddc.mm"
include "breq2.mm"
include "imbi1d.mm"
include "ralbidv.mm"
include "imbi2d.mm"
include "wa.mm"
include "nn0cnd.mm"
include "adantr.mm"
include "mul02d.mm"
include "simprr.mm"
include "ad2antrl.mm"
include "nn0ge0d.mm"
include "cr.mm"
include "wb.mm"
include "nn0red.mm"
include "0re.mm"
include "letri3.mm"
include "sylancl.mm"
include "mpbir2and.mm"
include "oveq1d.mm"
include "3eqtr4d.mm"
include "csn.mm"
include "cxp.mm"
include "cmpt.mm"
include "fconstmpt.mm"
include "0dgrb.mm"
include "mpbid.mm"
include "wf.mm"
include "plyf.mm"
include "ffvelrnda.mm"
include "feqmptd.mm"
include "syl6eq.mm"
include "eqidd.mm"
include "fmptco.mm"
include "3eqtr4a.mm"
include "fveq2d.mm"
include "eqtr2d.mm"
include "expr.mm"
include "ralrimiva.mm"
include "fveq2.mm"
include "breq1d.mm"
include "coeq1.mm"
include "eqeq12d.mm"
include "imbi12d.mm"
include "cbvralv.mm"
include "clt.mm"
include "wo.mm"
include "cn.mm"
include "nn0p1nn.mm"
include "ad2antlr.mm"
include "nnred.mm"
include "leloed.mm"
include "simplr.mm"
include "nn0leltp1.mm"
include "syl2anc.mm"
include "rspcva.mm"
include "adantl.mm"
include "sylbird.mm"
include "ccoe.mm"
include "eqid.mm"
include "simprll.mm"
include "ad2antrr.mm"
include "simprlr.mm"
include "sylib.mm"
include "dgrcolem2.mm"
include "jaod.mm"
include "sylbid.mm"
include "ralrimdva.mm"
include "syl5bi.mm"
include "expcom.mm"
include "a2d.mm"
include "nn0ind.mm"
include "mpcom.mm"
include "leidd.mm"
include "syl6eqr.mm"
include "rspcv.mm"
include "syl3c.mm"

theorem dgrco
  let wph: wff ph
  let cS: class S
  let cF: class F
  let cG: class G
  let cM: class M
  let cN: class N
  let vf: setvar f
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let vd: setvar d
  let vg: setvar g
  let vh: setvar h
  let cD: class D
  assume dgrco.1: |- M = ( deg ` F )
  assume dgrco.2: |- N = ( deg ` G )
  assume dgrco.3: |- ( ph -> F e. ( Poly ` S ) )
  assume dgrco.4: |- ( ph -> G e. ( Poly ` S ) )


  assert |- ( ph -> ( deg ` ( F o. G ) ) = ( M x. N ) )

  proof
    wph
    cF
    cc
    cply
    cfv
    #
    wcel
    vf
    cv
    #
    cdgr
    cfv
    #
    cM
    cle
    wbr
    #
    @1
    cG
    ccom
    #
    cdgr
    cfv
    #
    @2
    cN
    cmul
    co
    #
    wceq
    #
    wi
    #
    vf
    @0
    wral
    #
    cM
    cM
    cle
    wbr
    #
    cF
    cG
    ccom
    #
    cdgr
    cfv
    #
    cM
    cN
    cmul
    co
    #
    wceq
    #
    wph
    cS
    cply
    cfv
    #
    @0
    cF
    cS
    plyssc
    #
    dgrco.3
    sseldi
    cM
    cn0
    wcel
    wph
    @9
    wph
    cM
    cF
    cdgr
    cfv
    #
    cn0
    dgrco.1
    wph
    cF
    @15
    wcel
    @17
    cn0
    wcel
    dgrco.3
    cS
    cF
    dgrcl
    syl
    syl5eqel
    #
    wph
    @2
    vx
    cv
    #
    cle
    wbr
    #
    @7
    wi
    #
    vf
    @0
    wral
    #
    wi
    wph
    @2
    cc0
    cle
    wbr
    #
    @7
    wi
    #
    vf
    @0
    wral
    #
    wi
    wph
    @2
    vd
    cv
    #
    cle
    wbr
    #
    @7
    wi
    #
    vf
    @0
    wral
    #
    wi
    wph
    @2
    @26
    c1
    caddc
    co
    #
    cle
    wbr
    #
    @7
    wi
    #
    vf
    @0
    wral
    #
    wi
    wph
    @9
    wi
    vx
    vd
    cM
    @19
    cc0
    wceq
    #
    @22
    @25
    wph
    @34
    @21
    @24
    vf
    @0
    @34
    @20
    @23
    @7
    @19
    cc0
    @2
    cle
    breq2
    imbi1d
    ralbidv
    imbi2d
    @19
    @26
    wceq
    #
    @22
    @29
    wph
    @35
    @21
    @28
    vf
    @0
    @35
    @20
    @27
    @7
    @19
    @26
    @2
    cle
    breq2
    imbi1d
    ralbidv
    imbi2d
    @19
    @30
    wceq
    #
    @22
    @33
    wph
    @36
    @21
    @32
    vf
    @0
    @36
    @20
    @31
    @7
    @19
    @30
    @2
    cle
    breq2
    imbi1d
    ralbidv
    imbi2d
    @19
    cM
    wceq
    #
    @22
    @9
    wph
    @37
    @21
    @8
    vf
    @0
    @37
    @20
    @3
    @7
    @19
    cM
    @2
    cle
    breq2
    imbi1d
    ralbidv
    imbi2d
    wph
    @24
    vf
    @0
    wph
    @1
    @0
    wcel
    #
    @23
    @7
    wph
    @38
    @23
    wa
    #
    wa
    #
    @6
    @2
    @5
    @40
    cc0
    cN
    cmul
    co
    cc0
    @6
    @2
    @40
    cN
    wph
    cN
    cc
    wcel
    @39
    wph
    cN
    wph
    cN
    cG
    cdgr
    cfv
    #
    cn0
    dgrco.2
    wph
    cG
    @15
    wcel
    #
    @41
    cn0
    wcel
    dgrco.4
    cS
    cG
    dgrcl
    syl
    syl5eqel
    nn0cnd
    adantr
    mul02d
    @40
    @2
    cc0
    cN
    cmul
    @40
    @2
    cc0
    wceq
    #
    @23
    cc0
    @2
    cle
    wbr
    #
    wph
    @38
    @23
    simprr
    @40
    @2
    @38
    @2
    cn0
    wcel
    #
    wph
    @23
    cc
    @1
    dgrcl
    #
    ad2antrl
    #
    nn0ge0d
    @40
    @2
    cr
    wcel
    cc0
    cr
    wcel
    @43
    @23
    @44
    wa
    wb
    @40
    @2
    @47
    nn0red
    0re
    @2
    cc0
    letri3
    sylancl
    mpbir2and
    #
    oveq1d
    @48
    3eqtr4d
    @40
    @1
    @4
    cdgr
    @40
    cc
    cc0
    @1
    cfv
    #
    csn
    cxp
    #
    vy
    cc
    @49
    cmpt
    @1
    @4
    vy
    cc
    @49
    fconstmpt
    @40
    @43
    @1
    @50
    wceq
    #
    @48
    @38
    @43
    @51
    wb
    wph
    @23
    cc
    @1
    0dgrb
    ad2antrl
    mpbid
    #
    @40
    vy
    vx
    cc
    cc
    vy
    cv
    #
    cG
    cfv
    #
    @49
    @49
    cG
    @1
    @40
    cc
    cc
    @53
    cG
    @40
    @42
    cc
    cc
    cG
    wf
    wph
    @42
    @39
    dgrco.4
    adantr
    cS
    cG
    plyf
    syl
    #
    ffvelrnda
    @40
    vy
    cc
    cc
    cG
    @55
    feqmptd
    @40
    @1
    @50
    vx
    cc
    @49
    cmpt
    @52
    vx
    cc
    @49
    fconstmpt
    syl6eq
    @19
    @54
    wceq
    @49
    eqidd
    fmptco
    3eqtr4a
    fveq2d
    eqtr2d
    expr
    ralrimiva
    @26
    cn0
    wcel
    #
    wph
    @29
    @33
    wph
    @56
    @29
    @33
    wi
    @29
    vg
    cv
    #
    cdgr
    cfv
    #
    @26
    cle
    wbr
    #
    @57
    cG
    ccom
    #
    cdgr
    cfv
    #
    @58
    cN
    cmul
    co
    #
    wceq
    #
    wi
    #
    vg
    @0
    wral
    #
    wph
    @56
    wa
    #
    @33
    @28
    @64
    vf
    vg
    @0
    @1
    @57
    wceq
    #
    @27
    @59
    @7
    @63
    @67
    @2
    @58
    @26
    cle
    @1
    @57
    cdgr
    fveq2
    #
    breq1d
    @67
    @5
    @61
    @6
    @62
    @67
    @4
    @60
    cdgr
    @1
    @57
    cG
    coeq1
    fveq2d
    @67
    @2
    @58
    cN
    cmul
    @68
    oveq1d
    eqeq12d
    imbi12d
    cbvralv
    @66
    @65
    @32
    vf
    @0
    @66
    @38
    @65
    @32
    @66
    @38
    @65
    wa
    #
    wa
    #
    @31
    @2
    @30
    clt
    wbr
    #
    @2
    @30
    wceq
    #
    wo
    @7
    @70
    @2
    @30
    @70
    @2
    @38
    @45
    @66
    @65
    @46
    ad2antrl
    #
    nn0red
    @70
    @30
    @56
    @30
    cn
    wcel
    wph
    @69
    @26
    nn0p1nn
    ad2antlr
    nnred
    leloed
    @70
    @71
    @7
    @72
    @70
    @71
    @27
    @7
    @70
    @45
    @56
    @27
    @71
    wb
    @73
    wph
    @56
    @69
    simplr
    @2
    @26
    nn0leltp1
    syl2anc
    @69
    @28
    @66
    @64
    @28
    vg
    @1
    @0
    @57
    @1
    wceq
    #
    @59
    @27
    @63
    @7
    @74
    @58
    @2
    @26
    cle
    @57
    @1
    cdgr
    fveq2
    #
    breq1d
    @74
    @61
    @5
    @62
    @6
    @74
    @60
    @4
    cdgr
    @57
    @1
    cG
    coeq1
    fveq2d
    @74
    @58
    @2
    cN
    cmul
    @75
    oveq1d
    eqeq12d
    imbi12d
    rspcva
    adantl
    sylbird
    @66
    @69
    @72
    @7
    @66
    @69
    @72
    wa
    #
    wa
    #
    @1
    ccoe
    cfv
    #
    @26
    cc
    vh
    @1
    cG
    @2
    cN
    @2
    eqid
    dgrco.2
    @66
    @38
    @65
    @72
    simprll
    wph
    cG
    @0
    wcel
    @56
    @76
    wph
    @15
    @0
    cG
    @16
    dgrco.4
    sseldi
    ad2antrr
    @78
    eqid
    wph
    @56
    @76
    simplr
    @66
    @69
    @72
    simprr
    @77
    @65
    vh
    cv
    #
    cdgr
    cfv
    #
    @26
    cle
    wbr
    #
    @79
    cG
    ccom
    #
    cdgr
    cfv
    #
    @80
    cN
    cmul
    co
    #
    wceq
    #
    wi
    #
    vh
    @0
    wral
    @66
    @38
    @65
    @72
    simprlr
    @64
    @86
    vg
    vh
    @0
    @57
    @79
    wceq
    #
    @59
    @81
    @63
    @85
    @87
    @58
    @80
    @26
    cle
    @57
    @79
    cdgr
    fveq2
    #
    breq1d
    @87
    @61
    @83
    @62
    @84
    @87
    @60
    @82
    cdgr
    @57
    @79
    cG
    coeq1
    fveq2d
    @87
    @58
    @80
    cN
    cmul
    @88
    oveq1d
    eqeq12d
    imbi12d
    cbvralv
    sylib
    dgrcolem2
    expr
    jaod
    sylbid
    expr
    ralrimdva
    syl5bi
    expcom
    a2d
    nn0ind
    mpcom
    wph
    cM
    wph
    cM
    @18
    nn0red
    leidd
    @8
    @10
    @14
    wi
    vf
    cF
    @0
    @1
    cF
    wceq
    #
    @3
    @10
    @7
    @14
    @89
    @2
    cM
    cM
    cle
    @89
    @2
    @17
    cM
    @1
    cF
    cdgr
    fveq2
    dgrco.1
    syl6eqr
    #
    breq1d
    @89
    @5
    @12
    @6
    @13
    @89
    @4
    @11
    cdgr
    @1
    cF
    cG
    coeq1
    fveq2d
    @89
    @2
    cM
    cN
    cmul
    @90
    oveq1d
    eqeq12d
    imbi12d
    rspcv
    syl3c
end
