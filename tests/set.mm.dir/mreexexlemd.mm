include "cen.mm"
include "wbr.mm"
include "wo.mm"
include "cun.mm"
include "cfv.mm"
include "wss.mm"
include "wcel.mm"
include "cv.mm"
include "wa.mm"
include "cpw.mm"
include "wrex.mm"
include "w3a.mm"
include "wi.mm"
include "cdif.mm"
include "wral.mm"
include "wal.mm"
include "weq.mm"
include "simplr.mm"
include "breq1d.mm"
include "simpr.mm"
include "orbi12d.mm"
include "simpll.mm"
include "uneq12d.mm"
include "fveq2d.mm"
include "sseq12d.mm"
include "eleq1d.mm"
include "3anbi123d.mm"
include "simpllr.mm"
include "breq12d.mm"
include "simplll.mm"
include "anbi12d.mm"
include "pweqd.mm"
include "cbvrexdva2.mm"
include "imbi12d.mm"
include "wceq.mm"
include "simpl.mm"
include "difeq2d.mm"
include "adantr.mm"
include "cbvraldva2.mm"
include "cbvalv.mm"
include "sylib.mm"
include "cvv.mm"
include "ssun2.mm"
include "a1i.mm"
include "ssexd.mm"
include "difexg.mm"
include "syl.mm"
include "sselpwd.mm"
include "eleqtrrd.mm"
include "ad2antrr.mm"
include "uneq2d.mm"
include "rexeqbidv.mm"
include "rspcdv.mm"
include "rspcimdv.mm"
include "spcimdv.mm"
include "mpd.mm"
include "mp3and.mm"

theorem mreexexlemd
  let wph: wff ph
  let vv: setvar v
  let vu: setvar u
  let vt: setvar t
  let vi: setvar i
  let vj: setvar j
  let cF: class F
  let cG: class G
  let cH: class H
  let cI: class I
  let cJ: class J
  let cK: class K
  let cN: class N
  let cX: class X
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  assume mreexexlemd.1: |- ( ph -> X e. J )
  assume mreexexlemd.2: |- ( ph -> F C_ ( X \ H ) )
  assume mreexexlemd.3: |- ( ph -> G C_ ( X \ H ) )
  assume mreexexlemd.4: |- ( ph -> F C_ ( N ` ( G u. H ) ) )
  assume mreexexlemd.5: |- ( ph -> ( F u. H ) e. I )
  assume mreexexlemd.6: |- ( ph -> ( F ~~ K \/ G ~~ K ) )
  assume mreexexlemd.7: |- ( ph -> A. t A. u e. ~P ( X \ t ) A. v e. ~P ( X \ t ) ( ( ( u ~~ K \/ v ~~ K ) /\ u C_ ( N ` ( v u. t ) ) /\ ( u u. t ) e. I ) -> E. i e. ~P v ( u ~~ i /\ ( i u. t ) e. I ) ) )

  disjoint F j
  disjoint G j
  disjoint H j
  disjoint j ph
  disjoint t u
  disjoint t v
  disjoint i t
  disjoint I t
  disjoint j t
  disjoint u v
  disjoint i u
  disjoint I u
  disjoint j u
  disjoint i v
  disjoint I v
  disjoint j v
  disjoint I i
  disjoint i j
  disjoint I j
  disjoint K t
  disjoint K u
  disjoint K v
  disjoint N t
  disjoint N u
  disjoint N v
  disjoint X t
  disjoint X u
  disjoint X v
  disjoint F f
  disjoint f g
  disjoint f h
  disjoint f j
  disjoint F g
  disjoint F h
  disjoint g h
  disjoint g j
  disjoint h j
  disjoint G f
  disjoint G g
  disjoint G h
  disjoint H f
  disjoint H g
  disjoint H h
  disjoint f ph
  disjoint g ph
  disjoint h ph
  disjoint f t
  disjoint g t
  disjoint h t
  disjoint f u
  disjoint g u
  disjoint h u
  disjoint f v
  disjoint f i
  disjoint I f
  disjoint g v
  disjoint h v
  disjoint g i
  disjoint I g
  disjoint h i
  disjoint I h
  disjoint K f
  disjoint K g
  disjoint K h
  disjoint N f
  disjoint N g
  disjoint N h
  disjoint X f
  disjoint X g
  disjoint X h
  assert |- ( ph -> E. j e. ~P G ( F ~~ j /\ ( j u. H ) e. I ) )

  proof
    wph
    cF
    cK
    cen
    wbr
    #
    cG
    cK
    cen
    wbr
    #
    wo
    #
    cF
    cG
    cH
    cun
    #
    cN
    cfv
    #
    wss
    #
    cF
    cH
    cun
    #
    cI
    wcel
    #
    cF
    vj
    cv
    #
    cen
    wbr
    #
    @8
    cH
    cun
    #
    cI
    wcel
    #
    wa
    #
    vj
    cG
    cpw
    #
    wrex
    #
    mreexexlemd.6
    mreexexlemd.4
    mreexexlemd.5
    wph
    vf
    cv
    #
    cK
    cen
    wbr
    #
    vg
    cv
    #
    cK
    cen
    wbr
    #
    wo
    #
    @15
    @17
    vh
    cv
    #
    cun
    #
    cN
    cfv
    #
    wss
    #
    @15
    @20
    cun
    #
    cI
    wcel
    #
    w3a
    #
    @15
    @8
    cen
    wbr
    #
    @8
    @20
    cun
    #
    cI
    wcel
    #
    wa
    #
    vj
    @17
    cpw
    #
    wrex
    #
    wi
    #
    vg
    cX
    @20
    cdif
    #
    cpw
    #
    wral
    #
    vf
    @35
    wral
    #
    vh
    wal
    #
    @2
    @5
    @7
    w3a
    #
    @14
    wi
    #
    wph
    vu
    cv
    #
    cK
    cen
    wbr
    #
    vv
    cv
    #
    cK
    cen
    wbr
    #
    wo
    #
    @41
    @43
    vt
    cv
    #
    cun
    #
    cN
    cfv
    #
    wss
    #
    @41
    @46
    cun
    #
    cI
    wcel
    #
    w3a
    #
    @41
    vi
    cv
    #
    cen
    wbr
    #
    @53
    @46
    cun
    #
    cI
    wcel
    #
    wa
    #
    vi
    @43
    cpw
    #
    wrex
    #
    wi
    #
    vv
    cX
    @46
    cdif
    #
    cpw
    #
    wral
    #
    vu
    @62
    wral
    #
    vt
    wal
    @38
    mreexexlemd.7
    @64
    @37
    vt
    vh
    vt
    vh
    weq
    #
    @63
    @36
    vu
    vf
    @62
    @35
    @65
    vu
    vf
    weq
    #
    wa
    #
    @60
    @33
    vv
    vg
    @62
    @35
    @67
    vv
    vg
    weq
    #
    wa
    #
    @52
    @26
    @59
    @32
    @69
    @45
    @19
    @49
    @23
    @51
    @25
    @69
    @42
    @16
    @44
    @18
    @69
    @41
    @15
    cK
    cen
    @65
    @66
    @68
    simplr
    #
    breq1d
    @69
    @43
    @17
    cK
    cen
    @67
    @68
    simpr
    #
    breq1d
    orbi12d
    @69
    @41
    @15
    @48
    @22
    @70
    @69
    @47
    @21
    cN
    @69
    @43
    @17
    @46
    @20
    @71
    @65
    @66
    @68
    simpll
    #
    uneq12d
    fveq2d
    sseq12d
    @69
    @50
    @24
    cI
    @69
    @41
    @15
    @46
    @20
    @70
    @72
    uneq12d
    eleq1d
    3anbi123d
    @69
    @57
    @30
    vi
    vj
    @58
    @31
    @69
    vi
    vj
    weq
    #
    wa
    #
    @54
    @27
    @56
    @29
    @74
    @41
    @15
    @53
    @8
    cen
    @65
    @66
    @68
    @73
    simpllr
    @69
    @73
    simpr
    #
    breq12d
    @74
    @55
    @28
    cI
    @74
    @53
    @8
    @46
    @20
    @75
    @65
    @66
    @68
    @73
    simplll
    uneq12d
    eleq1d
    anbi12d
    @74
    @43
    @17
    @67
    @68
    @73
    simplr
    pweqd
    cbvrexdva2
    imbi12d
    @67
    @62
    @35
    wceq
    @68
    @67
    @61
    @34
    @67
    @46
    @20
    cX
    @65
    @66
    simpl
    difeq2d
    pweqd
    #
    adantr
    cbvraldva2
    @76
    cbvraldva2
    cbvalv
    sylib
    wph
    @37
    @40
    vh
    cH
    cvv
    wph
    cH
    @6
    cI
    mreexexlemd.5
    cH
    @6
    wss
    wph
    cH
    cF
    ssun2
    a1i
    ssexd
    wph
    @20
    cH
    wceq
    #
    wa
    #
    @36
    @40
    vf
    cF
    @35
    @78
    cF
    cX
    cH
    cdif
    #
    cpw
    #
    @35
    wph
    cF
    @80
    wcel
    @77
    wph
    cF
    @79
    cvv
    wph
    cX
    cJ
    wcel
    @79
    cvv
    wcel
    mreexexlemd.1
    cX
    cH
    cJ
    difexg
    syl
    #
    mreexexlemd.2
    sselpwd
    adantr
    @78
    @34
    @79
    @78
    @20
    cH
    cX
    wph
    @77
    simpr
    difeq2d
    pweqd
    #
    eleqtrrd
    @78
    @15
    cF
    wceq
    #
    wa
    #
    @33
    @40
    vg
    cG
    @35
    @84
    cG
    @80
    @35
    wph
    cG
    @80
    wcel
    @77
    @83
    wph
    cG
    @79
    cvv
    @81
    mreexexlemd.3
    sselpwd
    ad2antrr
    @78
    @35
    @80
    wceq
    @83
    @82
    adantr
    eleqtrrd
    @84
    @17
    cG
    wceq
    #
    wa
    #
    @26
    @39
    @32
    @14
    @86
    @19
    @2
    @23
    @5
    @25
    @7
    @86
    @16
    @0
    @18
    @1
    @86
    @15
    cF
    cK
    cen
    @78
    @83
    @85
    simplr
    #
    breq1d
    @86
    @17
    cG
    cK
    cen
    @84
    @85
    simpr
    #
    breq1d
    orbi12d
    @86
    @15
    cF
    @22
    @4
    @87
    @86
    @21
    @3
    cN
    @86
    @17
    cG
    @20
    cH
    @88
    wph
    @77
    @83
    @85
    simpllr
    #
    uneq12d
    fveq2d
    sseq12d
    @86
    @24
    @6
    cI
    @86
    @15
    cF
    @20
    cH
    @87
    @89
    uneq12d
    eleq1d
    3anbi123d
    @86
    @30
    @12
    vj
    @31
    @13
    @86
    @17
    cG
    @88
    pweqd
    @86
    @27
    @9
    @29
    @11
    @86
    @15
    cF
    @8
    cen
    @87
    breq1d
    @86
    @28
    @10
    cI
    @86
    @20
    cH
    @8
    @89
    uneq2d
    eleq1d
    anbi12d
    rexeqbidv
    imbi12d
    rspcdv
    rspcimdv
    spcimdv
    mpd
    mp3and
end
