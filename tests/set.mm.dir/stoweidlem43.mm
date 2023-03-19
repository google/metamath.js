include "cv.mm"
include "wcel.mm"
include "cfv.mm"
include "wne.mm"
include "cc0.mm"
include "wceq.mm"
include "w3a.mm"
include "wex.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "nfv.mm"
include "eldifad.mm"
include "cuni.mm"
include "elunii.mm"
include "syl2anc.mm"
include "syl6eleqr.mm"
include "wn.mm"
include "eldifbd.mm"
include "nelne2.mm"
include "necomd.mm"
include "3jca.mm"
include "wrex.mm"
include "simpr2.mm"
include "wi.mm"
include "nfan.mm"
include "nfim.mm"
include "eleq1.mm"
include "neeq2.mm"
include "3anbi23d.mm"
include "anbi2d.mm"
include "fveq2.mm"
include "neeq2d.mm"
include "rexbidv.mm"
include "imbi12d.mm"
include "simpr1.mm"
include "neeq1.mm"
include "3anbi13d.mm"
include "neeq1d.mm"
include "a1i.mm"
include "vtoclga.mm"
include "mpcom.mm"
include "vtoclg1f.mm"
include "df-rex.mm"
include "sylib.mm"
include "mpdan.mm"
include "cmin.mm"
include "co.mm"
include "cmpt.mm"
include "nfcv.mm"
include "eqid.mm"
include "cr.mm"
include "wf.mm"
include "ccn.mm"
include "sselda.mm"
include "fcnre.mm"
include "adantlr.mm"
include "caddc.mm"
include "3adant1r.mm"
include "adantr.mm"
include "simprl.mm"
include "simprr.mm"
include "stoweidlem23.mm"
include "fveq1.mm"
include "neeq12d.mm"
include "eqeq1d.mm"
include "3anbi123d.mm"
include "spcegv.mm"
include "3ad2ant1.mm"
include "pm2.43i.mm"
include "syl.mm"
include "exlimdd.mm"
include "cmul.mm"
include "crn.mm"
include "csup.mm"
include "cdiv.mm"
include "nfmpt1.mm"
include "weq.mm"
include "oveq12d.mm"
include "cbvmptv.mm"
include "ccmp.mm"
include "wss.mm"
include "3anbi2d.mm"
include "oveq1d.mm"
include "mpteq2dv.mm"
include "eleq1d.mm"
include "chvarv.mm"
include "simpr3.mm"
include "stoweidlem36.mm"
include "ex.mm"
include "exlimdv.mm"
include "mpd.mm"

theorem stoweidlem43
  let wph: wff ph
  let vx: setvar x
  let vt: setvar t
  let cA: class A
  let cQ: class Q
  let cS: class S
  let cT: class T
  let cU: class U
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let cJ: class J
  let cK: class K
  let cZ: class Z
  let vr: setvar r
  let vl: setvar l
  let vs: setvar s
  let vk: setvar k
  assume stoweidlem43.1: |- F/ g ph
  assume stoweidlem43.2: |- F/ t ph
  assume stoweidlem43.3: |- F/_ h Q
  assume stoweidlem43.4: |- K = ( topGen ` ran (,) )
  assume stoweidlem43.5: |- Q = { h e. A | ( ( h ` Z ) = 0 /\ A. t e. T ( 0 <_ ( h ` t ) /\ ( h ` t ) <_ 1 ) ) }
  assume stoweidlem43.6: |- T = U. J
  assume stoweidlem43.7: |- ( ph -> J e. Comp )
  assume stoweidlem43.8: |- ( ph -> A C_ ( J Cn K ) )
  assume stoweidlem43.9: |- ( ( ph /\ f e. A /\ l e. A ) -> ( t e. T |-> ( ( f ` t ) + ( l ` t ) ) ) e. A )
  assume stoweidlem43.10: |- ( ( ph /\ f e. A /\ l e. A ) -> ( t e. T |-> ( ( f ` t ) x. ( l ` t ) ) ) e. A )
  assume stoweidlem43.11: |- ( ( ph /\ x e. RR ) -> ( t e. T |-> x ) e. A )
  assume stoweidlem43.12: |- ( ( ph /\ ( r e. T /\ t e. T /\ r =/= t ) ) -> E. g e. A ( g ` r ) =/= ( g ` t ) )
  assume stoweidlem43.13: |- ( ph -> U e. J )
  assume stoweidlem43.14: |- ( ph -> Z e. U )
  assume stoweidlem43.15: |- ( ph -> S e. ( T \ U ) )

  disjoint f g
  disjoint f l
  disjoint f t
  disjoint A f
  disjoint g l
  disjoint g t
  disjoint A g
  disjoint l t
  disjoint A l
  disjoint A t
  disjoint f h
  disjoint T f
  disjoint h t
  disjoint T h
  disjoint T t
  disjoint T l
  disjoint f r
  disjoint g r
  disjoint r t
  disjoint A r
  disjoint f x
  disjoint g x
  disjoint t x
  disjoint A x
  disjoint Q f
  disjoint S f
  disjoint S g
  disjoint S l
  disjoint S t
  disjoint Z f
  disjoint Z g
  disjoint Z l
  disjoint Z t
  disjoint f ph
  disjoint l ph
  disjoint A h
  disjoint S h
  disjoint Z h
  disjoint T r
  disjoint S r
  disjoint ph r
  disjoint T x
  disjoint S x
  disjoint Z x
  disjoint ph x
  disjoint f s
  disjoint h s
  disjoint s t
  disjoint T s
  disjoint f k
  disjoint k l
  disjoint k s
  disjoint k t
  disjoint T k
  disjoint l s
  disjoint k ph
  disjoint A k
  disjoint S k
  disjoint Z k
  disjoint r s
  disjoint s x
  disjoint k x
  assert |- ( ph -> E. h ( h e. Q /\ 0 < ( h ` S ) ) )

  proof
    wph
    vf
    cv
    #
    cA
    wcel
    #
    cS
    @0
    cfv
    #
    cZ
    @0
    cfv
    #
    wne
    #
    @3
    cc0
    wceq
    #
    w3a
    #
    vf
    wex
    #
    vh
    cv
    #
    cQ
    wcel
    cc0
    cS
    @8
    cfv
    clt
    wbr
    wa
    vh
    wex
    #
    wph
    vg
    cv
    #
    cA
    wcel
    #
    cS
    @10
    cfv
    #
    cZ
    @10
    cfv
    #
    wne
    #
    wa
    #
    @7
    vg
    stoweidlem43.1
    @7
    vg
    nfv
    wph
    cS
    cT
    wcel
    #
    cZ
    cT
    wcel
    #
    cS
    cZ
    wne
    #
    w3a
    #
    @15
    vg
    wex
    #
    wph
    @16
    @17
    @18
    wph
    cS
    cT
    cU
    stoweidlem43.15
    eldifad
    #
    wph
    cZ
    cJ
    cuni
    #
    cT
    wph
    cZ
    cU
    wcel
    #
    cU
    cJ
    wcel
    cZ
    @22
    wcel
    stoweidlem43.14
    stoweidlem43.13
    cZ
    cU
    cJ
    elunii
    syl2anc
    stoweidlem43.6
    syl6eleqr
    #
    wph
    cZ
    cS
    wph
    @23
    cS
    cU
    wcel
    wn
    cZ
    cS
    wne
    stoweidlem43.14
    wph
    cS
    cT
    cU
    stoweidlem43.15
    eldifbd
    cZ
    cS
    cU
    nelne2
    syl2anc
    necomd
    3jca
    wph
    @19
    wa
    #
    @14
    vg
    cA
    wrex
    #
    @20
    @17
    @25
    @26
    wph
    @16
    @17
    @18
    simpr2
    wph
    @16
    vt
    cv
    #
    cT
    wcel
    #
    cS
    @27
    wne
    #
    w3a
    #
    wa
    #
    @12
    @27
    @10
    cfv
    #
    wne
    #
    vg
    cA
    wrex
    #
    wi
    #
    @25
    @26
    wi
    vt
    cZ
    cT
    @25
    @26
    vt
    wph
    @19
    vt
    stoweidlem43.2
    @19
    vt
    nfv
    nfan
    @26
    vt
    nfv
    nfim
    @27
    cZ
    wceq
    #
    @31
    @25
    @34
    @26
    @36
    @30
    @19
    wph
    @36
    @28
    @17
    @29
    @18
    @16
    @27
    cZ
    cT
    eleq1
    @27
    cZ
    cS
    neeq2
    3anbi23d
    anbi2d
    @36
    @33
    @14
    vg
    cA
    @36
    @32
    @13
    @12
    @27
    cZ
    @10
    fveq2
    neeq2d
    rexbidv
    imbi12d
    @16
    @31
    @34
    wph
    @16
    @28
    @29
    simpr1
    wph
    vr
    cv
    #
    cT
    wcel
    #
    @28
    @37
    @27
    wne
    #
    w3a
    #
    wa
    #
    @37
    @10
    cfv
    #
    @32
    wne
    #
    vg
    cA
    wrex
    #
    wi
    #
    @35
    vr
    cS
    cT
    @37
    cS
    wceq
    #
    @41
    @31
    @44
    @34
    @46
    @40
    @30
    wph
    @46
    @38
    @16
    @39
    @29
    @28
    @37
    cS
    cT
    eleq1
    @37
    cS
    @27
    neeq1
    3anbi13d
    anbi2d
    @46
    @43
    @33
    vg
    cA
    @46
    @42
    @12
    @32
    @37
    cS
    @10
    fveq2
    neeq1d
    rexbidv
    imbi12d
    @45
    @38
    stoweidlem43.12
    a1i
    vtoclga
    mpcom
    vtoclg1f
    mpcom
    @14
    vg
    cA
    df-rex
    sylib
    mpdan
    wph
    @15
    wa
    #
    vt
    cT
    @32
    @13
    cmin
    co
    cmpt
    #
    cA
    wcel
    #
    cS
    @48
    cfv
    #
    cZ
    @48
    cfv
    #
    wne
    #
    @51
    cc0
    wceq
    #
    w3a
    #
    @7
    @47
    vx
    vt
    cA
    cS
    cT
    vf
    vl
    @10
    @48
    cZ
    wph
    @15
    vt
    stoweidlem43.2
    @15
    vt
    nfv
    nfan
    vt
    @10
    nfcv
    @48
    eqid
    wph
    @1
    cT
    cr
    @0
    wf
    @15
    wph
    @1
    wa
    cJ
    cK
    ccn
    co
    #
    cT
    @0
    cJ
    cK
    stoweidlem43.4
    stoweidlem43.6
    @55
    eqid
    wph
    cA
    @55
    @0
    stoweidlem43.8
    sselda
    fcnre
    adantlr
    wph
    @1
    vl
    cv
    #
    cA
    wcel
    #
    vt
    cT
    @27
    @0
    cfv
    #
    @27
    @56
    cfv
    #
    caddc
    co
    cmpt
    cA
    wcel
    @15
    stoweidlem43.9
    3adant1r
    wph
    vx
    cv
    #
    cr
    wcel
    #
    vt
    cT
    @60
    cmpt
    cA
    wcel
    #
    @15
    stoweidlem43.11
    adantlr
    wph
    @16
    @15
    @21
    adantr
    wph
    @17
    @15
    @24
    adantr
    wph
    @11
    @14
    simprl
    wph
    @11
    @14
    simprr
    stoweidlem23
    @54
    @7
    @49
    @52
    @54
    @7
    wi
    @53
    @6
    @54
    vf
    @48
    cA
    @0
    @48
    wceq
    #
    @1
    @49
    @4
    @52
    @5
    @53
    @0
    @48
    cA
    eleq1
    @63
    @2
    @50
    @3
    @51
    cS
    @0
    @48
    fveq1
    cZ
    @0
    @48
    fveq1
    #
    neeq12d
    @63
    @3
    @51
    cc0
    @64
    eqeq1d
    3anbi123d
    spcegv
    3ad2ant1
    pm2.43i
    syl
    exlimdd
    wph
    @6
    @9
    vf
    wph
    @6
    @9
    wph
    @6
    wa
    vx
    vt
    cA
    cQ
    cS
    cT
    vk
    vl
    vh
    @0
    vs
    cT
    vs
    cv
    #
    @0
    cfv
    #
    @66
    cmul
    co
    #
    cmpt
    #
    vt
    cT
    @27
    @68
    cfv
    @68
    crn
    cr
    clt
    csup
    #
    cdiv
    co
    #
    cmpt
    #
    cJ
    cK
    @69
    cZ
    stoweidlem43.3
    vt
    cT
    @70
    nfmpt1
    vt
    @0
    nfcv
    vt
    @68
    nfcv
    wph
    @6
    vt
    stoweidlem43.2
    @6
    vt
    nfv
    nfan
    stoweidlem43.4
    stoweidlem43.5
    stoweidlem43.6
    vs
    vt
    cT
    @67
    @58
    @58
    cmul
    co
    vs
    vt
    weq
    @66
    @58
    @66
    @58
    cmul
    @65
    @27
    @0
    fveq2
    #
    @72
    oveq12d
    cbvmptv
    @69
    eqid
    @71
    eqid
    wph
    cJ
    ccmp
    wcel
    @6
    stoweidlem43.7
    adantr
    wph
    cA
    @55
    wss
    @6
    stoweidlem43.8
    adantr
    wph
    vk
    cv
    #
    cA
    wcel
    #
    @57
    vt
    cT
    @27
    @73
    cfv
    #
    @59
    cmul
    co
    #
    cmpt
    #
    cA
    wcel
    #
    @6
    wph
    @1
    @57
    w3a
    #
    vt
    cT
    @58
    @59
    cmul
    co
    #
    cmpt
    #
    cA
    wcel
    #
    wi
    wph
    @74
    @57
    w3a
    #
    @78
    wi
    vf
    vk
    vf
    vk
    weq
    #
    @79
    @83
    @82
    @78
    @84
    @1
    @74
    wph
    @57
    @0
    @73
    cA
    eleq1
    3anbi2d
    @84
    @81
    @77
    cA
    @84
    vt
    cT
    @80
    @76
    @84
    @58
    @75
    @59
    cmul
    @27
    @0
    @73
    fveq1
    oveq1d
    mpteq2dv
    eleq1d
    imbi12d
    stoweidlem43.10
    chvarv
    3adant1r
    wph
    @61
    @62
    @6
    stoweidlem43.11
    adantlr
    wph
    @16
    @6
    @21
    adantr
    wph
    @17
    @6
    @24
    adantr
    wph
    @1
    @4
    @5
    simpr1
    wph
    @1
    @4
    @5
    simpr2
    wph
    @1
    @4
    @5
    simpr3
    stoweidlem36
    ex
    exlimdv
    mpd
end
