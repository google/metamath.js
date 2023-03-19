include "cima.mm"
include "cvv.mm"
include "wcel.mm"
include "c0.mm"
include "wne.mm"
include "cv.mm"
include "cun.mm"
include "wss.mm"
include "wrex.mm"
include "wral.mm"
include "cipo.mm"
include "cfv.mm"
include "cdrs.mm"
include "elex.mm"
include "syl.mm"
include "w3a.mm"
include "isipodrs.mm"
include "sylib.mm"
include "simp2d.mm"
include "cpw.mm"
include "wfn.mm"
include "wceq.mm"
include "wb.mm"
include "fnimaeq0.mm"
include "syl2anc.mm"
include "necon3bid.mm"
include "mpbird.mm"
include "simp3d.mm"
include "wa.mm"
include "wi.mm"
include "simplll.mm"
include "simpr.mm"
include "ad2antrr.mm"
include "simprr.mm"
include "sseldd.mm"
include "elpwid.mm"
include "adantr.mm"
include "vex.mm"
include "weq.mm"
include "sseq12.mm"
include "sseq1.mm"
include "adantl.mm"
include "anbi12d.mm"
include "anbi2d.mm"
include "fveq2.mm"
include "syl2an.mm"
include "imbi12d.mm"
include "vtocl2.mm"
include "syl12anc.mm"
include "ex.mm"
include "anim12d.mm"
include "unss.mm"
include "3imtr3g.mm"
include "anassrs.mm"
include "reximdva.mm"
include "ralimdva.mm"
include "mpd.mm"
include "uneq1.mm"
include "sseq1d.mm"
include "rexbidv.mm"
include "ralbidv.mm"
include "ralima.mm"
include "uneq2.mm"
include "sseq2.mm"
include "rexima.mm"
include "bitrd.mm"
include "syl3anbrc.mm"

theorem ipodrsima
  let wph: wff ph
  let vv: setvar v
  let vu: setvar u
  let cA: class A
  let cB: class B
  let cF: class F
  let cV: class V
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume ipodrsima.f: |- ( ph -> F Fn ~P A )
  assume ipodrsima.m: |- ( ( ph /\ ( u C_ v /\ v C_ A ) ) -> ( F ` u ) C_ ( F ` v ) )
  assume ipodrsima.d: |- ( ph -> ( toInc ` B ) e. Dirset )
  assume ipodrsima.s: |- ( ph -> B C_ ~P A )
  assume ipodrsima.a: |- ( ph -> ( F " B ) e. V )

  disjoint ph u
  disjoint ph v
  disjoint u v
  disjoint A u
  disjoint A v
  disjoint F u
  disjoint F v
  disjoint a ph
  disjoint b ph
  disjoint c ph
  disjoint a b
  disjoint a c
  disjoint a u
  disjoint a v
  disjoint b c
  disjoint b u
  disjoint b v
  disjoint c u
  disjoint c v
  disjoint A a
  disjoint A b
  disjoint A c
  disjoint A x
  disjoint A y
  disjoint A z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint B a
  disjoint B b
  disjoint B c
  disjoint B z
  disjoint a z
  disjoint b z
  disjoint c z
  disjoint B x
  disjoint B y
  disjoint F a
  disjoint F b
  disjoint F c
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint a x
  disjoint a y
  disjoint b y
  assert |- ( ph -> ( toInc ` ( F " B ) ) e. Dirset )

  proof
    wph
    cF
    cB
    cima
    #
    cvv
    wcel
    #
    @0
    c0
    wne
    #
    vx
    cv
    #
    vy
    cv
    #
    cun
    #
    vz
    cv
    #
    wss
    #
    vz
    @0
    wrex
    #
    vy
    @0
    wral
    #
    vx
    @0
    wral
    #
    @0
    cipo
    cfv
    cdrs
    wcel
    wph
    @0
    cV
    wcel
    @1
    ipodrsima.a
    @0
    cV
    elex
    syl
    wph
    @2
    cB
    c0
    wne
    #
    wph
    cB
    cvv
    wcel
    #
    @11
    va
    cv
    #
    vb
    cv
    #
    cun
    vc
    cv
    #
    wss
    #
    vc
    cB
    wrex
    #
    vb
    cB
    wral
    #
    va
    cB
    wral
    #
    wph
    cB
    cipo
    cfv
    cdrs
    wcel
    @12
    @11
    @19
    w3a
    ipodrsima.d
    va
    vb
    vc
    cB
    isipodrs
    sylib
    #
    simp2d
    wph
    @0
    c0
    cB
    c0
    wph
    cF
    cA
    cpw
    #
    wfn
    #
    cB
    @21
    wss
    #
    @0
    c0
    wceq
    cB
    c0
    wceq
    wb
    ipodrsima.f
    ipodrsima.s
    @21
    cB
    cF
    fnimaeq0
    syl2anc
    necon3bid
    mpbird
    wph
    @10
    @13
    cF
    cfv
    #
    @14
    cF
    cfv
    #
    cun
    #
    @15
    cF
    cfv
    #
    wss
    #
    vc
    cB
    wrex
    #
    vb
    cB
    wral
    #
    va
    cB
    wral
    #
    wph
    @19
    @31
    wph
    @12
    @11
    @19
    @20
    simp3d
    wph
    @18
    @30
    va
    cB
    wph
    @13
    cB
    wcel
    #
    wa
    #
    @17
    @29
    vb
    cB
    @33
    @14
    cB
    wcel
    #
    wa
    @16
    @28
    vc
    cB
    @33
    @34
    @15
    cB
    wcel
    #
    @16
    @28
    wi
    @33
    @34
    @35
    wa
    #
    wa
    #
    @13
    @15
    wss
    #
    @14
    @15
    wss
    #
    wa
    @24
    @27
    wss
    #
    @25
    @27
    wss
    #
    wa
    @16
    @28
    @37
    @38
    @40
    @39
    @41
    @37
    @38
    @40
    @37
    @38
    wa
    wph
    @38
    @15
    cA
    wss
    #
    @40
    wph
    @32
    @36
    @38
    simplll
    @37
    @38
    simpr
    @37
    @42
    @38
    @37
    @15
    cA
    @37
    cB
    @21
    @15
    wph
    @23
    @32
    @36
    ipodrsima.s
    ad2antrr
    @33
    @34
    @35
    simprr
    sseldd
    elpwid
    #
    adantr
    wph
    vu
    cv
    #
    vv
    cv
    #
    wss
    #
    @45
    cA
    wss
    #
    wa
    #
    wa
    #
    @44
    cF
    cfv
    #
    @45
    cF
    cfv
    #
    wss
    #
    wi
    #
    wph
    @38
    @42
    wa
    #
    wa
    #
    @40
    wi
    vu
    vv
    @13
    @15
    va
    vex
    vc
    vex
    #
    vu
    va
    weq
    #
    vv
    vc
    weq
    #
    wa
    #
    @49
    @55
    @52
    @40
    @59
    @48
    @54
    wph
    @59
    @46
    @38
    @47
    @42
    @44
    @13
    @45
    @15
    sseq12
    @58
    @47
    @42
    wb
    #
    @57
    @45
    @15
    cA
    sseq1
    #
    adantl
    anbi12d
    anbi2d
    @57
    @50
    @24
    wceq
    @51
    @27
    wceq
    #
    @52
    @40
    wb
    @58
    @44
    @13
    cF
    fveq2
    @45
    @15
    cF
    fveq2
    #
    @50
    @24
    @51
    @27
    sseq12
    syl2an
    imbi12d
    ipodrsima.m
    vtocl2
    syl12anc
    ex
    @37
    @39
    @41
    @37
    @39
    wa
    wph
    @39
    @42
    @41
    wph
    @32
    @36
    @39
    simplll
    @37
    @39
    simpr
    @37
    @42
    @39
    @43
    adantr
    @53
    wph
    @39
    @42
    wa
    #
    wa
    #
    @41
    wi
    vu
    vv
    @14
    @15
    vb
    vex
    @56
    vu
    vb
    weq
    #
    @58
    wa
    #
    @49
    @65
    @52
    @41
    @67
    @48
    @64
    wph
    @67
    @46
    @39
    @47
    @42
    @44
    @14
    @45
    @15
    sseq12
    @58
    @60
    @66
    @61
    adantl
    anbi12d
    anbi2d
    @66
    @50
    @25
    wceq
    @62
    @52
    @41
    wb
    @58
    @44
    @14
    cF
    fveq2
    @63
    @50
    @25
    @51
    @27
    sseq12
    syl2an
    imbi12d
    ipodrsima.m
    vtocl2
    syl12anc
    ex
    anim12d
    @13
    @14
    @15
    unss
    @24
    @25
    @27
    unss
    3imtr3g
    anassrs
    reximdva
    ralimdva
    ralimdva
    mpd
    wph
    @10
    @24
    @4
    cun
    #
    @6
    wss
    #
    vz
    @0
    wrex
    #
    vy
    @0
    wral
    #
    va
    cB
    wral
    #
    @31
    wph
    @22
    @23
    @10
    @72
    wb
    ipodrsima.f
    ipodrsima.s
    @9
    @71
    vx
    va
    @21
    cB
    cF
    @3
    @24
    wceq
    #
    @8
    @70
    vy
    @0
    @73
    @7
    @69
    vz
    @0
    @73
    @5
    @68
    @6
    @3
    @24
    @4
    uneq1
    sseq1d
    rexbidv
    ralbidv
    ralima
    syl2anc
    wph
    @71
    @30
    va
    cB
    wph
    @71
    @26
    @6
    wss
    #
    vz
    @0
    wrex
    #
    vb
    cB
    wral
    #
    @30
    wph
    @22
    @23
    @71
    @76
    wb
    ipodrsima.f
    ipodrsima.s
    @70
    @75
    vy
    vb
    @21
    cB
    cF
    @4
    @25
    wceq
    #
    @69
    @74
    vz
    @0
    @77
    @68
    @26
    @6
    @4
    @25
    @24
    uneq2
    sseq1d
    rexbidv
    ralima
    syl2anc
    wph
    @75
    @29
    vb
    cB
    wph
    @22
    @23
    @75
    @29
    wb
    ipodrsima.f
    ipodrsima.s
    @74
    @28
    vz
    vc
    @21
    cB
    cF
    @6
    @27
    @26
    sseq2
    rexima
    syl2anc
    ralbidv
    bitrd
    ralbidv
    bitrd
    mpbird
    vx
    vy
    vz
    @0
    isipodrs
    syl3anbrc
end
