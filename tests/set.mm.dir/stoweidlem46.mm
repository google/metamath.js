include "cdif.mm"
include "cuni.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wex.mm"
include "cc0.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "nfv.mm"
include "nfan.mm"
include "nfcv.mm"
include "nfdif.mm"
include "nfel2.mm"
include "ccmp.mm"
include "adantr.mm"
include "ccn.mm"
include "co.mm"
include "wss.mm"
include "caddc.mm"
include "cmpt.mm"
include "3adant1r.mm"
include "cmul.mm"
include "cr.mm"
include "adantlr.mm"
include "wne.mm"
include "w3a.mm"
include "wrex.mm"
include "simpr.mm"
include "stoweidlem43.mm"
include "weq.mm"
include "eleq1.mm"
include "fveq1.mm"
include "breq2d.mm"
include "anbi12d.mm"
include "cbvex.mm"
include "sylib.mm"
include "crab.mm"
include "cvv.mm"
include "rabexg.mm"
include "syl.mm"
include "ad2antrr.mm"
include "eldifi.mm"
include "ad2antlr.mm"
include "simprr.mm"
include "fveq2.mm"
include "elrab.mm"
include "sylanbrc.mm"
include "wceq.mm"
include "simpll.mm"
include "cle.mm"
include "c1.mm"
include "wral.mm"
include "syl6eleq.mm"
include "eqeq1d.mm"
include "breq1d.mm"
include "ralbidv.mm"
include "simpld.mm"
include "sseldd.mm"
include "ad2ant2r.mm"
include "eqid.mm"
include "cxr.mm"
include "0xr.mm"
include "a1i.mm"
include "rfcnpre1.mm"
include "syl2anc.mm"
include "eqidd.mm"
include "rabbidv.mm"
include "eqeq2d.mm"
include "rspcegf.mm"
include "eqeq1.mm"
include "rexbidv.mm"
include "syl6eleqr.mm"
include "nfrab1.mm"
include "nfcxfr.mm"
include "eleq2.mm"
include "spcegf.mm"
include "imp.mm"
include "syl12anc.mm"
include "exlimddv.mm"
include "elunif.mm"
include "sylibr.mm"
include "ex.mm"
include "ssrdv.mm"

theorem stoweidlem46
  let wph: wff ph
  let vx: setvar x
  let vw: setvar w
  let vt: setvar t
  let cA: class A
  let cQ: class Q
  let cT: class T
  let cU: class U
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let cJ: class J
  let cK: class K
  let cW: class W
  let cZ: class Z
  let vr: setvar r
  let vq: setvar q
  let vs: setvar s
  let vk: setvar k
  assume stoweidlem46.1: |- F/_ t U
  assume stoweidlem46.2: |- F/_ h Q
  assume stoweidlem46.3: |- F/ q ph
  assume stoweidlem46.4: |- F/ t ph
  assume stoweidlem46.5: |- K = ( topGen ` ran (,) )
  assume stoweidlem46.6: |- Q = { h e. A | ( ( h ` Z ) = 0 /\ A. t e. T ( 0 <_ ( h ` t ) /\ ( h ` t ) <_ 1 ) ) }
  assume stoweidlem46.7: |- W = { w e. J | E. h e. Q w = { t e. T | 0 < ( h ` t ) } }
  assume stoweidlem46.8: |- T = U. J
  assume stoweidlem46.9: |- ( ph -> J e. Comp )
  assume stoweidlem46.10: |- ( ph -> A C_ ( J Cn K ) )
  assume stoweidlem46.11: |- ( ( ph /\ f e. A /\ g e. A ) -> ( t e. T |-> ( ( f ` t ) + ( g ` t ) ) ) e. A )
  assume stoweidlem46.12: |- ( ( ph /\ f e. A /\ g e. A ) -> ( t e. T |-> ( ( f ` t ) x. ( g ` t ) ) ) e. A )
  assume stoweidlem46.13: |- ( ( ph /\ x e. RR ) -> ( t e. T |-> x ) e. A )
  assume stoweidlem46.14: |- ( ( ph /\ ( r e. T /\ t e. T /\ r =/= t ) ) -> E. q e. A ( q ` r ) =/= ( q ` t ) )
  assume stoweidlem46.15: |- ( ph -> U e. J )
  assume stoweidlem46.16: |- ( ph -> Z e. U )
  assume stoweidlem46.17: |- ( ph -> T e. _V )

  disjoint f g
  disjoint f h
  disjoint f t
  disjoint T f
  disjoint g h
  disjoint g t
  disjoint T g
  disjoint h t
  disjoint T h
  disjoint T t
  disjoint f q
  disjoint g q
  disjoint q t
  disjoint T q
  disjoint f r
  disjoint q r
  disjoint r t
  disjoint T r
  disjoint f x
  disjoint q x
  disjoint t x
  disjoint T x
  disjoint A f
  disjoint A g
  disjoint A h
  disjoint A t
  disjoint Q f
  disjoint Q g
  disjoint U f
  disjoint U g
  disjoint U q
  disjoint Z f
  disjoint Z g
  disjoint Z h
  disjoint Z t
  disjoint f ph
  disjoint g ph
  disjoint g w
  disjoint h w
  disjoint t w
  disjoint T w
  disjoint W g
  disjoint A q
  disjoint A r
  disjoint Z q
  disjoint Z x
  disjoint U r
  disjoint ph r
  disjoint J t
  disjoint J w
  disjoint K t
  disjoint Q w
  disjoint A x
  disjoint U x
  disjoint ph x
  disjoint f s
  disjoint g s
  disjoint h s
  disjoint s t
  disjoint T s
  disjoint q s
  disjoint r s
  disjoint s x
  disjoint U s
  disjoint ph s
  disjoint s w
  disjoint W s
  disjoint k x
  assert |- ( ph -> ( T \ U ) C_ U. W )

  proof
    wph
    vs
    cT
    cU
    cdif
    #
    cW
    cuni
    #
    wph
    vs
    cv
    #
    @0
    wcel
    #
    @2
    @1
    wcel
    #
    wph
    @3
    wa
    #
    @2
    vw
    cv
    #
    wcel
    #
    @6
    cW
    wcel
    #
    wa
    #
    vw
    wex
    #
    @4
    @5
    vg
    cv
    #
    cQ
    wcel
    #
    cc0
    @2
    @11
    cfv
    #
    clt
    wbr
    #
    wa
    #
    @10
    vg
    @5
    vh
    cv
    #
    cQ
    wcel
    #
    cc0
    @2
    @16
    cfv
    #
    clt
    wbr
    #
    wa
    #
    vh
    wex
    @15
    vg
    wex
    @5
    vx
    vt
    cA
    cQ
    @2
    cT
    cU
    vf
    vq
    vh
    cJ
    cK
    cZ
    vr
    vg
    wph
    @3
    vq
    stoweidlem46.3
    @3
    vq
    nfv
    nfan
    wph
    @3
    vt
    stoweidlem46.4
    vt
    @2
    @0
    vt
    cT
    cU
    vt
    cT
    nfcv
    stoweidlem46.1
    nfdif
    nfel2
    nfan
    stoweidlem46.2
    stoweidlem46.5
    stoweidlem46.6
    stoweidlem46.8
    wph
    cJ
    ccmp
    wcel
    @3
    stoweidlem46.9
    adantr
    wph
    cA
    cJ
    cK
    ccn
    co
    #
    wss
    #
    @3
    stoweidlem46.10
    adantr
    wph
    vf
    cv
    #
    cA
    wcel
    #
    @11
    cA
    wcel
    #
    vt
    cT
    vt
    cv
    #
    @23
    cfv
    #
    @26
    @11
    cfv
    #
    caddc
    co
    cmpt
    cA
    wcel
    @3
    stoweidlem46.11
    3adant1r
    wph
    @24
    @25
    vt
    cT
    @27
    @28
    cmul
    co
    cmpt
    cA
    wcel
    @3
    stoweidlem46.12
    3adant1r
    wph
    vx
    cv
    #
    cr
    wcel
    vt
    cT
    @29
    cmpt
    cA
    wcel
    @3
    stoweidlem46.13
    adantlr
    wph
    vr
    cv
    #
    cT
    wcel
    @26
    cT
    wcel
    @30
    @26
    wne
    w3a
    @30
    vq
    cv
    #
    cfv
    @26
    @31
    cfv
    wne
    vq
    cA
    wrex
    @3
    stoweidlem46.14
    adantlr
    wph
    cU
    cJ
    wcel
    @3
    stoweidlem46.15
    adantr
    wph
    cZ
    cU
    wcel
    @3
    stoweidlem46.16
    adantr
    wph
    @3
    simpr
    stoweidlem43
    @20
    @15
    vh
    vg
    @20
    vg
    nfv
    @12
    @14
    vh
    vh
    @11
    cQ
    stoweidlem46.2
    nfel2
    @14
    vh
    nfv
    nfan
    vh
    vg
    weq
    #
    @17
    @12
    @19
    @14
    @16
    @11
    cQ
    eleq1
    @32
    @18
    @13
    cc0
    clt
    @2
    @16
    @11
    fveq1
    breq2d
    anbi12d
    cbvex
    sylib
    @5
    @15
    wa
    #
    cc0
    @28
    clt
    wbr
    #
    vt
    cT
    crab
    #
    cvv
    wcel
    #
    @2
    @35
    wcel
    #
    @35
    cW
    wcel
    #
    @10
    wph
    @36
    @3
    @15
    wph
    cT
    cvv
    wcel
    @36
    stoweidlem46.17
    @34
    vt
    cT
    cvv
    rabexg
    syl
    ad2antrr
    @33
    @2
    cT
    wcel
    #
    @14
    @37
    @3
    @39
    wph
    @15
    @2
    cT
    cU
    eldifi
    ad2antlr
    @5
    @12
    @14
    simprr
    @34
    @14
    vt
    @2
    cT
    vt
    vs
    weq
    @28
    @13
    cc0
    clt
    @26
    @2
    @11
    fveq2
    breq2d
    elrab
    sylanbrc
    @33
    @35
    @6
    cc0
    @26
    @16
    cfv
    #
    clt
    wbr
    #
    vt
    cT
    crab
    #
    wceq
    #
    vh
    cQ
    wrex
    #
    vw
    cJ
    crab
    #
    cW
    @33
    @35
    cJ
    wcel
    #
    @35
    @42
    wceq
    #
    vh
    cQ
    wrex
    #
    @35
    @45
    wcel
    @33
    wph
    @11
    @21
    wcel
    #
    @46
    wph
    @3
    @15
    simpll
    wph
    @12
    @49
    @3
    @14
    wph
    @12
    wa
    #
    cA
    @21
    @11
    wph
    @22
    @12
    stoweidlem46.10
    adantr
    @50
    @25
    cZ
    @11
    cfv
    #
    cc0
    wceq
    #
    cc0
    @28
    cle
    wbr
    #
    @28
    c1
    cle
    wbr
    #
    wa
    #
    vt
    cT
    wral
    #
    wa
    #
    @50
    @11
    cZ
    @16
    cfv
    #
    cc0
    wceq
    #
    cc0
    @40
    cle
    wbr
    #
    @40
    c1
    cle
    wbr
    #
    wa
    #
    vt
    cT
    wral
    #
    wa
    #
    vh
    cA
    crab
    #
    wcel
    @25
    @57
    wa
    @50
    @11
    cQ
    @65
    wph
    @12
    simpr
    #
    stoweidlem46.6
    syl6eleq
    @64
    @57
    vh
    @11
    cA
    @32
    @59
    @52
    @63
    @56
    @32
    @58
    @51
    cc0
    cZ
    @16
    @11
    fveq1
    eqeq1d
    @32
    @62
    @55
    vt
    cT
    @32
    @60
    @53
    @61
    @54
    @32
    @40
    @28
    cc0
    cle
    @26
    @16
    @11
    fveq1
    #
    breq2d
    @32
    @40
    @28
    c1
    cle
    @67
    breq1d
    anbi12d
    ralbidv
    anbi12d
    elrab
    sylib
    simpld
    sseldd
    ad2ant2r
    wph
    @49
    wa
    #
    vt
    @35
    cc0
    @11
    cJ
    cK
    cT
    vt
    cc0
    nfcv
    vt
    @11
    nfcv
    wph
    @49
    vt
    stoweidlem46.4
    @49
    vt
    nfv
    nfan
    stoweidlem46.5
    stoweidlem46.8
    @35
    eqid
    cc0
    cxr
    wcel
    @68
    0xr
    a1i
    wph
    @49
    simpr
    rfcnpre1
    syl2anc
    wph
    @12
    @48
    @3
    @14
    @50
    @12
    @35
    @35
    wceq
    #
    @48
    @66
    @50
    @35
    eqidd
    @47
    @69
    vh
    @11
    cQ
    @69
    vh
    nfv
    vh
    @11
    nfcv
    stoweidlem46.2
    @32
    @42
    @35
    @35
    @32
    @41
    @34
    vt
    cT
    @32
    @40
    @28
    cc0
    clt
    @67
    breq2d
    rabbidv
    eqeq2d
    rspcegf
    syl2anc
    ad2ant2r
    @44
    @48
    vw
    @35
    cJ
    @6
    @35
    wceq
    #
    @43
    @47
    vh
    cQ
    @6
    @35
    @42
    eqeq1
    rexbidv
    elrab
    sylanbrc
    stoweidlem46.7
    syl6eleqr
    @36
    @37
    @38
    wa
    #
    @10
    @9
    @71
    vw
    @35
    cvv
    vw
    @35
    nfcv
    @37
    @38
    vw
    @37
    vw
    nfv
    vw
    @35
    cW
    vw
    cW
    @45
    stoweidlem46.7
    @44
    vw
    cJ
    nfrab1
    nfcxfr
    #
    nfel2
    nfan
    @70
    @7
    @37
    @8
    @38
    @6
    @35
    @2
    eleq2
    @6
    @35
    cW
    eleq1
    anbi12d
    spcegf
    imp
    syl12anc
    exlimddv
    vw
    @2
    cW
    vw
    @2
    nfcv
    @72
    elunif
    sylibr
    ex
    ssrdv
end
