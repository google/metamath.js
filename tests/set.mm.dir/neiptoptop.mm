include "ctop.mm"
include "wcel.mm"
include "cv.mm"
include "wss.mm"
include "cuni.mm"
include "wi.mm"
include "wal.mm"
include "cin.mm"
include "wral.mm"
include "wa.mm"
include "cfv.mm"
include "uniss.mm"
include "adantl.mm"
include "wceq.mm"
include "neiptopuni.mm"
include "adantr.mm"
include "sseqtr4d.mm"
include "w3a.mm"
include "simp-4l.mm"
include "ad3antrrr.mm"
include "simpllr.mm"
include "sseldd.mm"
include "jca.mm"
include "elssuni.mm"
include "ad2antlr.mm"
include "3jca.mm"
include "simpr.mm"
include "sselda.mm"
include "neipeltop.mm"
include "simprbi.mm"
include "syl.mm"
include "r19.21bi.mm"
include "adantllr.mm"
include "sseq1.mm"
include "3anbi2d.mm"
include "eleq1.mm"
include "anbi12d.mm"
include "imbi1d.mm"
include "imbi2d.mm"
include "cvv.mm"
include "cpw.mm"
include "crab.mm"
include "ssid.mm"
include "a1i.mm"
include "ralrimiva.mm"
include "sylanbrc.mm"
include "pwexg.mm"
include "rabexg.mm"
include "3syl.mm"
include "syl5eqel.mm"
include "ssexd.mm"
include "uniexg.mm"
include "sseq2.mm"
include "3anbi23d.mm"
include "anbi1d.mm"
include "imbi12d.mm"
include "vtoclg.mm"
include "chvarv.mm"
include "mp2and.mm"
include "wrex.mm"
include "eluni2.mm"
include "sylib.mm"
include "r19.29a.mm"
include "ex.mm"
include "alrimiv.mm"
include "inss1.mm"
include "simplbi.mm"
include "syl5ss.mm"
include "cfi.mm"
include "simplll.mm"
include "sseldi.mm"
include "syl2anc.mm"
include "simplr.mm"
include "inss2.mm"
include "fvex.mm"
include "inelfi.mm"
include "mp3an1.mm"
include "wb.mm"
include "istopg.mm"
include "mpbir2and.mm"

theorem neiptoptop
  let wph: wff ph
  let cJ: class J
  let cN: class N
  let cX: class X
  let vq: setvar q
  let vp: setvar p
  let va: setvar a
  let vb: setvar b
  let cC: class C
  let vc: setvar c
  let ve: setvar e
  let vf: setvar f
  assume neiptop.o: |- J = { a e. ~P X | A. p e. a a e. ( N ` p ) }
  assume neiptop.0: |- ( ph -> N : X --> ~P ~P X )
  assume neiptop.1: |- ( ( ( ( ph /\ p e. X ) /\ a C_ b /\ b C_ X ) /\ a e. ( N ` p ) ) -> b e. ( N ` p ) )
  assume neiptop.2: |- ( ( ph /\ p e. X ) -> ( fi ` ( N ` p ) ) C_ ( N ` p ) )
  assume neiptop.3: |- ( ( ( ph /\ p e. X ) /\ a e. ( N ` p ) ) -> p e. a )
  assume neiptop.4: |- ( ( ( ph /\ p e. X ) /\ a e. ( N ` p ) ) -> E. b e. ( N ` p ) A. q e. b a e. ( N ` q ) )
  assume neiptop.5: |- ( ( ph /\ p e. X ) -> X e. ( N ` p ) )

  disjoint a p
  disjoint N a
  disjoint X a
  disjoint a b
  disjoint b p
  disjoint J a
  disjoint J p
  disjoint X p
  disjoint p ph
  disjoint N b
  disjoint X b
  disjoint a ph
  disjoint b ph
  disjoint C a
  disjoint C p
  disjoint a c
  disjoint a e
  disjoint a f
  disjoint c e
  disjoint c f
  disjoint c p
  disjoint J c
  disjoint e f
  disjoint e p
  disjoint J e
  disjoint f p
  disjoint J f
  disjoint b c
  disjoint N c
  disjoint b e
  disjoint b f
  disjoint c ph
  disjoint e ph
  disjoint f ph
  assert |- ( ph -> J e. Top )

  proof
    wph
    cJ
    ctop
    wcel
    #
    ve
    cv
    #
    cJ
    wss
    #
    @1
    cuni
    #
    cJ
    wcel
    #
    wi
    #
    ve
    wal
    #
    @1
    vf
    cv
    #
    cin
    #
    cJ
    wcel
    #
    vf
    cJ
    wral
    #
    ve
    cJ
    wral
    #
    wph
    @5
    ve
    wph
    @2
    @4
    wph
    @2
    wa
    #
    @3
    cX
    wss
    #
    @3
    vp
    cv
    #
    cN
    cfv
    #
    wcel
    #
    vp
    @3
    wral
    @4
    @12
    @3
    cJ
    cuni
    #
    cX
    @2
    @3
    @17
    wss
    wph
    @1
    cJ
    uniss
    adantl
    wph
    cX
    @17
    wceq
    @2
    wph
    cJ
    cN
    cX
    vq
    vp
    va
    vb
    neiptop.o
    neiptop.0
    neiptop.1
    neiptop.2
    neiptop.3
    neiptop.4
    neiptop.5
    neiptopuni
    adantr
    sseqtr4d
    #
    @12
    @16
    vp
    @3
    @12
    @14
    @3
    wcel
    #
    wa
    #
    @14
    vc
    cv
    #
    wcel
    #
    @16
    vc
    @1
    @20
    @21
    @1
    wcel
    #
    wa
    @22
    wa
    #
    wph
    @14
    cX
    wcel
    #
    wa
    #
    @21
    @3
    wss
    #
    @13
    w3a
    #
    @21
    @15
    wcel
    #
    @16
    @24
    @26
    @27
    @13
    @24
    wph
    @25
    wph
    @2
    @19
    @23
    @22
    simp-4l
    @24
    @3
    cX
    @14
    @12
    @13
    @19
    @23
    @22
    @18
    ad3antrrr
    #
    @12
    @19
    @23
    @22
    simpllr
    sseldd
    jca
    @23
    @27
    @20
    @22
    @21
    @1
    elssuni
    ad2antlr
    @30
    3jca
    @12
    @23
    @22
    @29
    @19
    @12
    @23
    wa
    #
    @29
    vp
    @21
    @31
    @21
    cJ
    wcel
    #
    @29
    vp
    @21
    wral
    #
    @12
    @1
    cJ
    @21
    wph
    @2
    simpr
    #
    sselda
    @32
    @21
    cX
    wss
    @33
    @21
    cJ
    cN
    cX
    vp
    va
    neiptop.o
    neipeltop
    simprbi
    syl
    r19.21bi
    adantllr
    @12
    @28
    @29
    wa
    #
    @16
    wi
    #
    @19
    @23
    @22
    @12
    @26
    va
    cv
    #
    @3
    wss
    #
    @13
    w3a
    #
    @37
    @15
    wcel
    #
    wa
    #
    @16
    wi
    #
    wi
    @12
    @36
    wi
    va
    vc
    @37
    @21
    wceq
    #
    @42
    @36
    @12
    @43
    @41
    @35
    @16
    @43
    @39
    @28
    @40
    @29
    @43
    @38
    @27
    @26
    @13
    @37
    @21
    @3
    sseq1
    3anbi2d
    @37
    @21
    @15
    eleq1
    anbi12d
    imbi1d
    imbi2d
    @12
    @1
    cvv
    wcel
    @3
    cvv
    wcel
    @42
    @12
    @1
    cJ
    cvv
    wph
    cJ
    cvv
    wcel
    #
    @2
    wph
    cJ
    @40
    vp
    @37
    wral
    #
    va
    cX
    cpw
    #
    crab
    #
    cvv
    neiptop.o
    wph
    cX
    cJ
    wcel
    #
    @46
    cvv
    wcel
    @47
    cvv
    wcel
    wph
    cX
    cX
    wss
    #
    cX
    @15
    wcel
    #
    vp
    cX
    wral
    @48
    @49
    wph
    cX
    ssid
    a1i
    wph
    @50
    vp
    cX
    neiptop.5
    ralrimiva
    cX
    cJ
    cN
    cX
    vp
    va
    neiptop.o
    neipeltop
    sylanbrc
    cX
    cJ
    pwexg
    @45
    va
    @46
    cvv
    rabexg
    3syl
    syl5eqel
    #
    adantr
    @34
    ssexd
    @1
    cvv
    uniexg
    @26
    @37
    vb
    cv
    #
    wss
    #
    @52
    cX
    wss
    #
    w3a
    #
    @40
    wa
    #
    @52
    @15
    wcel
    #
    wi
    @42
    vb
    @3
    cvv
    @52
    @3
    wceq
    #
    @56
    @41
    @57
    @16
    @58
    @55
    @39
    @40
    @58
    @53
    @38
    @54
    @13
    @26
    @52
    @3
    @37
    sseq2
    @52
    @3
    cX
    sseq1
    3anbi23d
    anbi1d
    @52
    @3
    @15
    eleq1
    imbi12d
    neiptop.1
    vtoclg
    3syl
    chvarv
    ad3antrrr
    mp2and
    @20
    @19
    @22
    vc
    @1
    wrex
    @12
    @19
    simpr
    vc
    @14
    @1
    eluni2
    sylib
    r19.29a
    ralrimiva
    @3
    cJ
    cN
    cX
    vp
    va
    neiptop.o
    neipeltop
    sylanbrc
    ex
    alrimiv
    wph
    @10
    ve
    cJ
    wph
    @1
    cJ
    wcel
    #
    wa
    #
    @9
    vf
    cJ
    @60
    @7
    cJ
    wcel
    #
    wa
    #
    @8
    cX
    wss
    @8
    @15
    wcel
    #
    vp
    @8
    wral
    @9
    @62
    @8
    @1
    cX
    @1
    @7
    inss1
    #
    @59
    @1
    cX
    wss
    #
    wph
    @61
    @59
    @65
    @1
    @15
    wcel
    #
    vp
    @1
    wral
    #
    @1
    cJ
    cN
    cX
    vp
    va
    neiptop.o
    neipeltop
    #
    simplbi
    #
    ad2antlr
    syl5ss
    @62
    @63
    vp
    @8
    @62
    @14
    @8
    wcel
    #
    wa
    #
    @15
    cfi
    cfv
    #
    @15
    @8
    @71
    wph
    @25
    @72
    @15
    wss
    wph
    @59
    @61
    @70
    simplll
    @71
    @1
    cX
    @14
    @71
    @59
    @65
    wph
    @59
    @61
    @70
    simpllr
    #
    @69
    syl
    @71
    @8
    @1
    @14
    @64
    @62
    @70
    simpr
    #
    sseldi
    #
    sseldd
    neiptop.2
    syl2anc
    @71
    @66
    @7
    @15
    wcel
    #
    @8
    @72
    wcel
    #
    @71
    @59
    @14
    @1
    wcel
    @66
    @73
    @75
    @59
    @66
    vp
    @1
    @59
    @65
    @67
    @68
    simprbi
    r19.21bi
    syl2anc
    @71
    @61
    @14
    @7
    wcel
    @76
    @60
    @61
    @70
    simplr
    @71
    @8
    @7
    @14
    @1
    @7
    inss2
    @74
    sseldi
    @61
    @76
    vp
    @7
    @61
    @7
    cX
    wss
    @76
    vp
    @7
    wral
    @7
    cJ
    cN
    cX
    vp
    va
    neiptop.o
    neipeltop
    simprbi
    r19.21bi
    syl2anc
    @15
    cvv
    wcel
    @66
    @76
    @77
    @14
    cN
    fvex
    @1
    @7
    cvv
    @15
    inelfi
    mp3an1
    syl2anc
    sseldd
    ralrimiva
    @8
    cJ
    cN
    cX
    vp
    va
    neiptop.o
    neipeltop
    sylanbrc
    ralrimiva
    ralrimiva
    wph
    @44
    @0
    @6
    @11
    wa
    wb
    @51
    ve
    vf
    cvv
    cJ
    istopg
    syl
    mpbir2and
end
