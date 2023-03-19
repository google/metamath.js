include "cnacs.mm"
include "cfv.mm"
include "wcel.mm"
include "cn0.mm"
include "wf.mm"
include "cv.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "wss.mm"
include "wral.mm"
include "w3a.mm"
include "crn.mm"
include "cuni.mm"
include "wceq.mm"
include "cuz.mm"
include "wa.mm"
include "fvssunirn.mm"
include "simplrr.mm"
include "syl5sseqr.mm"
include "simpll3.mm"
include "simplrl.mm"
include "simpr.mm"
include "incssnn0.mm"
include "syl3anc.mm"
include "eqssd.mm"
include "ralrimiva.mm"
include "wrex.mm"
include "cipo.mm"
include "cdrs.mm"
include "cvv.mm"
include "c0.mm"
include "wne.mm"
include "cun.mm"
include "cpw.mm"
include "frn.mm"
include "3ad2ant2.mm"
include "wb.mm"
include "elpw2g.mm"
include "3ad2ant1.mm"
include "mpbird.mm"
include "elex.mm"
include "syl.mm"
include "cc0.mm"
include "wfn.mm"
include "ffn.mm"
include "0nn0.mm"
include "fnfvelrn.mm"
include "sylancl.mm"
include "ne0i.mm"
include "cr.mm"
include "nn0re.mm"
include "ad2antrl.mm"
include "ad2antll.mm"
include "cle.mm"
include "wbr.mm"
include "cz.mm"
include "nn0z.mm"
include "eluz.mm"
include "syl2an.mm"
include "biimpar.mm"
include "adantll.mm"
include "ssequn1.mm"
include "sylib.mm"
include "eqimss.mm"
include "weq.mm"
include "fveq2.mm"
include "sseq2d.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "syl2anr.mm"
include "ssequn2.mm"
include "lecasei.mm"
include "ralrimivva.mm"
include "uneq1.mm"
include "sseq1d.mm"
include "rexbidv.mm"
include "ralbidv.mm"
include "ralrn.mm"
include "uneq2.mm"
include "sseq2.mm"
include "rexrn.mm"
include "bitrd.mm"
include "isipodrs.mm"
include "syl3anbrc.mm"
include "wi.mm"
include "cmre.mm"
include "isnacs3.mm"
include "simprbi.mm"
include "eleq1d.mm"
include "unieq.mm"
include "id.mm"
include "eleq12d.mm"
include "imbi12d.mm"
include "rspcva.mm"
include "mpd.mm"
include "fvelrnb.mm"
include "mpbid.mm"
include "reximddv.mm"

theorem nacsfix
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cC: class C
  let cF: class F
  let cX: class X
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vw: setvar w

  disjoint C z
  disjoint C y
  disjoint F y
  disjoint F z
  disjoint y z
  disjoint X z
  disjoint X y
  disjoint x y
  disjoint x z
  disjoint F x
  disjoint C a
  disjoint C b
  disjoint a b
  disjoint a z
  disjoint b z
  disjoint F a
  disjoint F b
  disjoint F c
  disjoint F w
  disjoint a c
  disjoint a w
  disjoint b c
  disjoint b w
  disjoint c w
  disjoint X a
  disjoint X b
  disjoint a x
  disjoint a y
  disjoint b x
  disjoint w y
  disjoint w z
  assert |- ( ( C e. ( NoeACS ` X ) /\ F : NN0 --> C /\ A. x e. NN0 ( F ` x ) C_ ( F ` ( x + 1 ) ) ) -> E. y e. NN0 A. z e. ( ZZ>= ` y ) ( F ` z ) = ( F ` y ) )

  proof
    cC
    cX
    cnacs
    cfv
    #
    wcel
    #
    cn0
    cC
    cF
    wf
    #
    vx
    cv
    #
    cF
    cfv
    @3
    c1
    caddc
    co
    cF
    cfv
    wss
    vx
    cn0
    wral
    #
    w3a
    #
    vy
    cv
    #
    cF
    cfv
    #
    cF
    crn
    #
    cuni
    #
    wceq
    #
    vz
    cv
    #
    cF
    cfv
    #
    @7
    wceq
    #
    vz
    @6
    cuz
    cfv
    #
    wral
    vy
    cn0
    @5
    @6
    cn0
    wcel
    #
    @10
    wa
    #
    wa
    #
    @13
    vz
    @14
    @17
    @11
    @14
    wcel
    #
    wa
    #
    @12
    @7
    @19
    @9
    @12
    @7
    cF
    @11
    fvssunirn
    @5
    @15
    @10
    @18
    simplrr
    syl5sseqr
    @19
    @4
    @15
    @18
    @7
    @12
    wss
    @1
    @2
    @4
    @16
    @18
    simpll3
    @5
    @15
    @10
    @18
    simplrl
    @17
    @18
    simpr
    vx
    @6
    @11
    cF
    incssnn0
    syl3anc
    eqssd
    ralrimiva
    @5
    @9
    @8
    wcel
    #
    @10
    vy
    cn0
    wrex
    #
    @5
    @8
    cipo
    cfv
    #
    cdrs
    wcel
    #
    @20
    @5
    @8
    cvv
    wcel
    #
    @8
    c0
    wne
    #
    @6
    @11
    cun
    #
    vw
    cv
    #
    wss
    #
    vw
    @8
    wrex
    #
    vz
    @8
    wral
    #
    vy
    @8
    wral
    #
    @23
    @5
    @8
    cC
    cpw
    #
    wcel
    #
    @24
    @5
    @33
    @8
    cC
    wss
    #
    @2
    @1
    @34
    @4
    cn0
    cC
    cF
    frn
    3ad2ant2
    @1
    @2
    @33
    @34
    wb
    @4
    @8
    cC
    @0
    elpw2g
    3ad2ant1
    mpbird
    #
    @8
    @32
    elex
    syl
    @5
    cc0
    cF
    cfv
    #
    @8
    wcel
    #
    @25
    @5
    cF
    cn0
    wfn
    #
    cc0
    cn0
    wcel
    @37
    @2
    @1
    @38
    @4
    cn0
    cC
    cF
    ffn
    3ad2ant2
    #
    0nn0
    cn0
    cc0
    cF
    fnfvelrn
    sylancl
    @8
    @36
    ne0i
    syl
    @5
    @31
    va
    cv
    #
    cF
    cfv
    #
    vb
    cv
    #
    cF
    cfv
    #
    cun
    #
    vc
    cv
    #
    cF
    cfv
    #
    wss
    #
    vc
    cn0
    wrex
    #
    vb
    cn0
    wral
    #
    va
    cn0
    wral
    #
    @5
    @48
    va
    vb
    cn0
    cn0
    @5
    @40
    cn0
    wcel
    #
    @42
    cn0
    wcel
    #
    wa
    #
    wa
    #
    @48
    @40
    @42
    @51
    @40
    cr
    wcel
    @5
    @52
    @40
    nn0re
    ad2antrl
    @52
    @42
    cr
    wcel
    @5
    @51
    @42
    nn0re
    ad2antll
    @54
    @40
    @42
    cle
    wbr
    #
    wa
    #
    @52
    @44
    @43
    wss
    #
    @48
    @5
    @51
    @52
    @55
    simplrr
    @56
    @44
    @43
    wceq
    #
    @57
    @56
    @41
    @43
    wss
    #
    @58
    @56
    @4
    @51
    @42
    @40
    cuz
    cfv
    wcel
    #
    @59
    @1
    @2
    @4
    @53
    @55
    simpll3
    @5
    @51
    @52
    @55
    simplrl
    @53
    @55
    @60
    @5
    @53
    @60
    @55
    @51
    @40
    cz
    wcel
    #
    @42
    cz
    wcel
    #
    @60
    @55
    wb
    @52
    @40
    nn0z
    #
    @42
    nn0z
    #
    @40
    @42
    eluz
    syl2an
    biimpar
    adantll
    vx
    @40
    @42
    cF
    incssnn0
    syl3anc
    @41
    @43
    ssequn1
    sylib
    @44
    @43
    eqimss
    syl
    @47
    @57
    vc
    @42
    cn0
    vc
    vb
    weq
    @46
    @43
    @44
    @45
    @42
    cF
    fveq2
    sseq2d
    rspcev
    syl2anc
    @54
    @42
    @40
    cle
    wbr
    #
    wa
    #
    @51
    @44
    @41
    wss
    #
    @48
    @5
    @51
    @52
    @65
    simplrl
    @66
    @44
    @41
    wceq
    #
    @67
    @66
    @43
    @41
    wss
    #
    @68
    @66
    @4
    @52
    @40
    @42
    cuz
    cfv
    wcel
    #
    @69
    @1
    @2
    @4
    @53
    @65
    simpll3
    @5
    @51
    @52
    @65
    simplrr
    @53
    @65
    @70
    @5
    @53
    @70
    @65
    @52
    @62
    @61
    @70
    @65
    wb
    @51
    @64
    @63
    @42
    @40
    eluz
    syl2anr
    biimpar
    adantll
    vx
    @42
    @40
    cF
    incssnn0
    syl3anc
    @43
    @41
    ssequn2
    sylib
    @44
    @41
    eqimss
    syl
    @47
    @67
    vc
    @40
    cn0
    vc
    va
    weq
    @46
    @41
    @44
    @45
    @40
    cF
    fveq2
    sseq2d
    rspcev
    syl2anc
    lecasei
    ralrimivva
    @5
    @38
    @31
    @50
    wb
    @39
    @38
    @31
    @41
    @11
    cun
    #
    @27
    wss
    #
    vw
    @8
    wrex
    #
    vz
    @8
    wral
    #
    va
    cn0
    wral
    @50
    @30
    @74
    vy
    va
    cn0
    cF
    @6
    @41
    wceq
    #
    @29
    @73
    vz
    @8
    @75
    @28
    @72
    vw
    @8
    @75
    @26
    @71
    @27
    @6
    @41
    @11
    uneq1
    sseq1d
    rexbidv
    ralbidv
    ralrn
    @38
    @74
    @49
    va
    cn0
    @38
    @74
    @44
    @27
    wss
    #
    vw
    @8
    wrex
    #
    vb
    cn0
    wral
    @49
    @73
    @77
    vz
    vb
    cn0
    cF
    @11
    @43
    wceq
    #
    @72
    @76
    vw
    @8
    @78
    @71
    @44
    @27
    @11
    @43
    @41
    uneq2
    sseq1d
    rexbidv
    ralrn
    @38
    @77
    @48
    vb
    cn0
    @76
    @47
    vw
    vc
    cn0
    cF
    @27
    @46
    @44
    sseq2
    rexrn
    ralbidv
    bitrd
    ralbidv
    bitrd
    syl
    mpbird
    vy
    vz
    vw
    @8
    isipodrs
    syl3anbrc
    @5
    @33
    @6
    cipo
    cfv
    #
    cdrs
    wcel
    #
    @6
    cuni
    #
    @6
    wcel
    #
    wi
    #
    vy
    @32
    wral
    #
    @23
    @20
    wi
    #
    @35
    @1
    @2
    @84
    @4
    @1
    cC
    cX
    cmre
    cfv
    wcel
    @84
    cC
    cX
    vy
    isnacs3
    simprbi
    3ad2ant1
    @83
    @85
    vy
    @8
    @32
    @6
    @8
    wceq
    #
    @80
    @23
    @82
    @20
    @86
    @79
    @22
    cdrs
    @6
    @8
    cipo
    fveq2
    eleq1d
    @86
    @81
    @9
    @6
    @8
    @6
    @8
    unieq
    @86
    id
    eleq12d
    imbi12d
    rspcva
    syl2anc
    mpd
    @5
    @38
    @20
    @21
    wb
    @39
    vy
    cn0
    @9
    cF
    fvelrnb
    syl
    mpbid
    reximddv
end
