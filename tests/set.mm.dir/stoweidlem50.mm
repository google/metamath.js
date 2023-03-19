include "cdif.mm"
include "cuni.mm"
include "wss.mm"
include "cv.mm"
include "cfn.mm"
include "wcel.mm"
include "w3a.mm"
include "wex.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "cle.mm"
include "wbr.mm"
include "c1.mm"
include "wa.mm"
include "wral.mm"
include "crab.mm"
include "nfrab1.mm"
include "nfcxfr.mm"
include "nfv.mm"
include "ccn.mm"
include "co.mm"
include "syl6sseq.mm"
include "cvv.mm"
include "ccmp.mm"
include "uniexg.mm"
include "syl.mm"
include "syl5eqel.mm"
include "stoweidlem46.mm"
include "cpw.mm"
include "cin.mm"
include "wrex.mm"
include "wi.mm"
include "crest.mm"
include "ccld.mm"
include "dfin4.mm"
include "elssuni.mm"
include "syl6sseqr.mm"
include "sseqin2.mm"
include "sylib.mm"
include "syl5eqr.mm"
include "eqeltrd.mm"
include "ctop.mm"
include "wb.mm"
include "cmptop.mm"
include "difssd.mm"
include "iscld2.mm"
include "syl2anc.mm"
include "mpbird.mm"
include "cmpcld.mm"
include "cmpsub.mm"
include "mpbid.mm"
include "clt.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "rabexd.mm"
include "elpwg.mm"
include "mpbiri.mm"
include "unieq.mm"
include "sseq2d.mm"
include "pweq.mm"
include "ineq1d.mm"
include "rexeqdv.mm"
include "imbi12d.mm"
include "rspccva.mm"
include "imp.mm"
include "df-rex.mm"
include "elinel2.mm"
include "ad2antrl.mm"
include "elinel1.mm"
include "elpwid.mm"
include "simprr.mm"
include "3jca.mm"
include "ex.mm"
include "eximdv.mm"
include "mpd.mm"
include "mpdan.mm"

theorem stoweidlem50
  let wph: wff ph
  let vx: setvar x
  let vw: setvar w
  let vu: setvar u
  let vt: setvar t
  let cA: class A
  let cC: class C
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
  let vc: setvar c
  let vk: setvar k
  assume stoweidlem50.1: |- F/_ t U
  assume stoweidlem50.2: |- F/ t ph
  assume stoweidlem50.3: |- K = ( topGen ` ran (,) )
  assume stoweidlem50.4: |- Q = { h e. A | ( ( h ` Z ) = 0 /\ A. t e. T ( 0 <_ ( h ` t ) /\ ( h ` t ) <_ 1 ) ) }
  assume stoweidlem50.5: |- W = { w e. J | E. h e. Q w = { t e. T | 0 < ( h ` t ) } }
  assume stoweidlem50.6: |- T = U. J
  assume stoweidlem50.7: |- C = ( J Cn K )
  assume stoweidlem50.8: |- ( ph -> J e. Comp )
  assume stoweidlem50.9: |- ( ph -> A C_ C )
  assume stoweidlem50.10: |- ( ( ph /\ f e. A /\ g e. A ) -> ( t e. T |-> ( ( f ` t ) + ( g ` t ) ) ) e. A )
  assume stoweidlem50.11: |- ( ( ph /\ f e. A /\ g e. A ) -> ( t e. T |-> ( ( f ` t ) x. ( g ` t ) ) ) e. A )
  assume stoweidlem50.12: |- ( ( ph /\ x e. RR ) -> ( t e. T |-> x ) e. A )
  assume stoweidlem50.13: |- ( ( ph /\ ( r e. T /\ t e. T /\ r =/= t ) ) -> E. q e. A ( q ` r ) =/= ( q ` t ) )
  assume stoweidlem50.14: |- ( ph -> U e. J )
  assume stoweidlem50.15: |- ( ph -> Z e. U )

  disjoint J u
  disjoint T u
  disjoint U u
  disjoint W u
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
  disjoint A f
  disjoint q r
  disjoint A q
  disjoint r t
  disjoint A r
  disjoint A t
  disjoint f x
  disjoint q x
  disjoint t x
  disjoint T x
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
  disjoint ph q
  disjoint g w
  disjoint h w
  disjoint t w
  disjoint T w
  disjoint A g
  disjoint A h
  disjoint W g
  disjoint Z q
  disjoint Z x
  disjoint T r
  disjoint U r
  disjoint ph r
  disjoint J t
  disjoint J w
  disjoint K t
  disjoint ph u
  disjoint Q w
  disjoint A x
  disjoint U x
  disjoint ph x
  disjoint c u
  disjoint J c
  disjoint T c
  disjoint U c
  disjoint W c
  disjoint k x
  assert |- ( ph -> E. u ( u e. Fin /\ u C_ W /\ ( T \ U ) C_ U. u ) )

  proof
    wph
    cT
    cU
    cdif
    #
    cW
    cuni
    #
    wss
    #
    vu
    cv
    #
    cfn
    wcel
    #
    @3
    cW
    wss
    #
    @0
    @3
    cuni
    wss
    #
    w3a
    #
    vu
    wex
    #
    wph
    vx
    vw
    vt
    cA
    cQ
    cT
    cU
    vf
    vg
    vh
    cJ
    cK
    cW
    cZ
    vr
    vq
    stoweidlem50.1
    vh
    cQ
    cZ
    vh
    cv
    #
    cfv
    cc0
    wceq
    cc0
    vt
    cv
    @9
    cfv
    #
    cle
    wbr
    @10
    c1
    cle
    wbr
    wa
    vt
    cT
    wral
    wa
    #
    vh
    cA
    crab
    stoweidlem50.4
    @11
    vh
    cA
    nfrab1
    nfcxfr
    wph
    vq
    nfv
    stoweidlem50.2
    stoweidlem50.3
    stoweidlem50.4
    stoweidlem50.5
    stoweidlem50.6
    stoweidlem50.8
    wph
    cA
    cC
    cJ
    cK
    ccn
    co
    stoweidlem50.9
    stoweidlem50.7
    syl6sseq
    stoweidlem50.10
    stoweidlem50.11
    stoweidlem50.12
    stoweidlem50.13
    stoweidlem50.14
    stoweidlem50.15
    wph
    cT
    cJ
    cuni
    #
    cvv
    stoweidlem50.6
    wph
    cJ
    ccmp
    wcel
    #
    @12
    cvv
    wcel
    stoweidlem50.8
    cJ
    ccmp
    uniexg
    syl
    syl5eqel
    stoweidlem46
    wph
    @2
    wa
    #
    @3
    cW
    cpw
    #
    cfn
    cin
    #
    wcel
    #
    @6
    wa
    #
    vu
    wex
    #
    @8
    @14
    @6
    vu
    @16
    wrex
    #
    @19
    wph
    @2
    @20
    wph
    @0
    vc
    cv
    #
    cuni
    #
    wss
    #
    @6
    vu
    @21
    cpw
    #
    cfn
    cin
    #
    wrex
    #
    wi
    #
    vc
    cJ
    cpw
    #
    wral
    #
    cW
    @28
    wcel
    #
    @2
    @20
    wi
    #
    wph
    cJ
    @0
    crest
    co
    ccmp
    wcel
    #
    @29
    wph
    @13
    @0
    cJ
    ccld
    cfv
    wcel
    #
    @32
    stoweidlem50.8
    wph
    @33
    cT
    @0
    cdif
    #
    cJ
    wcel
    #
    wph
    @34
    cU
    cJ
    wph
    @34
    cT
    cU
    cin
    #
    cU
    cT
    cU
    dfin4
    wph
    cU
    cT
    wss
    @36
    cU
    wceq
    wph
    cU
    @12
    cT
    wph
    cU
    cJ
    wcel
    cU
    @12
    wss
    stoweidlem50.14
    cU
    cJ
    elssuni
    syl
    stoweidlem50.6
    syl6sseqr
    cU
    cT
    sseqin2
    sylib
    syl5eqr
    stoweidlem50.14
    eqeltrd
    wph
    cJ
    ctop
    wcel
    #
    @0
    cT
    wss
    #
    @33
    @35
    wb
    wph
    @13
    @37
    stoweidlem50.8
    cJ
    cmptop
    syl
    #
    wph
    cT
    cU
    difssd
    #
    @0
    cJ
    cT
    stoweidlem50.6
    iscld2
    syl2anc
    mpbird
    @0
    cJ
    cmpcld
    syl2anc
    wph
    @37
    @38
    @32
    @29
    wb
    @39
    @40
    @0
    cJ
    cT
    vc
    vu
    stoweidlem50.6
    cmpsub
    syl2anc
    mpbid
    wph
    @30
    cW
    cJ
    wss
    #
    cW
    vw
    cv
    cc0
    @10
    clt
    wbr
    vt
    cT
    crab
    wceq
    vh
    cQ
    wrex
    #
    vw
    cJ
    crab
    cJ
    stoweidlem50.5
    @42
    vw
    cJ
    ssrab2
    eqsstri
    wph
    cW
    cvv
    wcel
    @30
    @41
    wb
    wph
    @42
    vw
    cJ
    cW
    ccmp
    stoweidlem50.5
    stoweidlem50.8
    rabexd
    cW
    cJ
    cvv
    elpwg
    syl
    mpbiri
    @27
    @31
    vc
    cW
    @28
    @21
    cW
    wceq
    #
    @23
    @2
    @26
    @20
    @43
    @22
    @1
    @0
    @21
    cW
    unieq
    sseq2d
    @43
    @6
    vu
    @25
    @16
    @43
    @24
    @15
    cfn
    @21
    cW
    pweq
    ineq1d
    rexeqdv
    imbi12d
    rspccva
    syl2anc
    imp
    @6
    vu
    @16
    df-rex
    sylib
    @14
    @18
    @7
    vu
    @14
    @18
    @7
    @14
    @18
    wa
    #
    @4
    @5
    @6
    @17
    @4
    @14
    @6
    @3
    @15
    cfn
    elinel2
    ad2antrl
    @44
    @3
    cW
    @17
    @3
    @15
    wcel
    @14
    @6
    @3
    @15
    cfn
    elinel1
    ad2antrl
    elpwid
    @14
    @17
    @6
    simprr
    3jca
    ex
    eximdv
    mpd
    mpdan
end
