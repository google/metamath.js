include "co.mm"
include "wcel.mm"
include "cv.mm"
include "wa.mm"
include "wrex.mm"
include "wi.mm"
include "wral.mm"
include "cstrkgb.mm"
include "cstrkg.mm"
include "cstrkgc.mm"
include "cin.mm"
include "cstrkgcb.mm"
include "clng.mm"
include "cfv.mm"
include "csn.mm"
include "cdif.mm"
include "w3o.mm"
include "crab.mm"
include "cmpt2.mm"
include "wceq.mm"
include "citv.mm"
include "wsbc.mm"
include "cbs.mm"
include "cab.mm"
include "df-trkg.mm"
include "inss1.mm"
include "inss2.mm"
include "sstri.mm"
include "eqsstri.mm"
include "sseldi.mm"
include "cpw.mm"
include "cvv.mm"
include "w3a.mm"
include "istrkgb.mm"
include "simprbi.mm"
include "simp2d.mm"
include "syl.mm"
include "oveq1.mm"
include "eleq2d.mm"
include "anbi1d.mm"
include "oveq2.mm"
include "anbi2d.mm"
include "rexbidv.mm"
include "imbi12d.mm"
include "2ralbidv.mm"
include "anbi12d.mm"
include "imbi1d.mm"
include "rspc3v.mm"
include "syl3anc.mm"
include "mpd.mm"
include "eleq1.mm"
include "rspc2v.mm"
include "syl2anc.mm"
include "mp2and.mm"

theorem axtgpasch
  let wph: wff ph
  let cP: class P
  let cU: class U
  let cG: class G
  let cI: class I
  let c.mi: class .-
  let cV: class V
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let va: setvar a
  let vf: setvar f
  let vi: setvar i
  let vp: setvar p
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vb: setvar b
  let vc: setvar c
  let vv: setvar v
  let cA: class A
  let cB: class B
  let cC: class C
  let vs: setvar s
  let vt: setvar t
  let vu: setvar u
  let cS: class S
  let cT: class T
  assume axtrkg.p: |- P = ( Base ` G )
  assume axtrkg.d: |- .- = ( dist ` G )
  assume axtrkg.i: |- I = ( Itv ` G )
  assume axtrkg.g: |- ( ph -> G e. TarskiG )
  assume axtgpasch.1: |- ( ph -> X e. P )
  assume axtgpasch.2: |- ( ph -> Y e. P )
  assume axtgpasch.3: |- ( ph -> Z e. P )
  assume axtgpasch.4: |- ( ph -> U e. P )
  assume axtgpasch.5: |- ( ph -> V e. P )
  assume axtgpasch.6: |- ( ph -> U e. ( X I Z ) )
  assume axtgpasch.7: |- ( ph -> V e. ( Y I Z ) )

  disjoint I a
  disjoint P a
  disjoint U a
  disjoint X a
  disjoint Y a
  disjoint Z a
  disjoint V a
  disjoint .- a
  disjoint f i
  disjoint f p
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint i p
  disjoint i x
  disjoint i y
  disjoint i z
  disjoint p x
  disjoint p y
  disjoint p z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint a b
  disjoint a c
  disjoint a v
  disjoint a z
  disjoint A a
  disjoint b c
  disjoint b v
  disjoint b z
  disjoint A b
  disjoint c v
  disjoint c z
  disjoint A c
  disjoint v z
  disjoint A v
  disjoint A z
  disjoint B b
  disjoint B c
  disjoint B v
  disjoint B z
  disjoint C c
  disjoint C v
  disjoint a s
  disjoint a t
  disjoint a u
  disjoint a x
  disjoint a y
  disjoint b s
  disjoint b t
  disjoint b u
  disjoint b x
  disjoint b y
  disjoint I b
  disjoint c s
  disjoint c t
  disjoint c u
  disjoint c x
  disjoint c y
  disjoint I c
  disjoint s t
  disjoint s u
  disjoint s v
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint I s
  disjoint t u
  disjoint t v
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint I t
  disjoint u v
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint I u
  disjoint v x
  disjoint v y
  disjoint I v
  disjoint I x
  disjoint I y
  disjoint I z
  disjoint P b
  disjoint P c
  disjoint P s
  disjoint P t
  disjoint P u
  disjoint P v
  disjoint P x
  disjoint P y
  disjoint P z
  disjoint S a
  disjoint S b
  disjoint S s
  disjoint S t
  disjoint S x
  disjoint T a
  disjoint T b
  disjoint T t
  disjoint T x
  disjoint T y
  disjoint U b
  disjoint U c
  disjoint U u
  disjoint U v
  disjoint X b
  disjoint X c
  disjoint X u
  disjoint X v
  disjoint X x
  disjoint X y
  disjoint X z
  disjoint Y b
  disjoint Y c
  disjoint Y u
  disjoint Y v
  disjoint Y y
  disjoint Y z
  disjoint Z b
  disjoint Z c
  disjoint Z u
  disjoint Z v
  disjoint Z z
  disjoint V b
  disjoint V v
  disjoint .- b
  disjoint .- c
  disjoint .- u
  disjoint .- v
  disjoint .- x
  disjoint .- y
  disjoint .- z
  assert |- ( ph -> E. a e. P ( a e. ( U I Y ) /\ a e. ( V I X ) ) )

  proof
    wph
    cU
    cX
    cZ
    cI
    co
    #
    wcel
    #
    cV
    cY
    cZ
    cI
    co
    #
    wcel
    #
    va
    cv
    #
    cU
    cY
    cI
    co
    #
    wcel
    #
    @4
    cV
    cX
    cI
    co
    #
    wcel
    #
    wa
    #
    va
    cP
    wrex
    #
    axtgpasch.6
    axtgpasch.7
    wph
    vu
    cv
    #
    @0
    wcel
    #
    vv
    cv
    #
    @2
    wcel
    #
    wa
    #
    @4
    @11
    cY
    cI
    co
    #
    wcel
    #
    @4
    @13
    cX
    cI
    co
    #
    wcel
    #
    wa
    #
    va
    cP
    wrex
    #
    wi
    #
    vv
    cP
    wral
    vu
    cP
    wral
    #
    @1
    @3
    wa
    #
    @10
    wi
    #
    wph
    @11
    vx
    cv
    #
    vz
    cv
    #
    cI
    co
    #
    wcel
    #
    @13
    vy
    cv
    #
    @27
    cI
    co
    #
    wcel
    #
    wa
    #
    @4
    @11
    @30
    cI
    co
    #
    wcel
    #
    @4
    @13
    @26
    cI
    co
    #
    wcel
    #
    wa
    #
    va
    cP
    wrex
    #
    wi
    #
    vv
    cP
    wral
    vu
    cP
    wral
    #
    vz
    cP
    wral
    vy
    cP
    wral
    vx
    cP
    wral
    #
    @23
    wph
    cG
    cstrkgb
    wcel
    #
    @42
    wph
    cstrkg
    cstrkgb
    cG
    cstrkg
    cstrkgc
    cstrkgb
    cin
    #
    cstrkgcb
    vf
    cv
    #
    clng
    cfv
    vx
    vy
    vp
    cv
    #
    @46
    @26
    csn
    cdif
    @27
    @26
    @30
    vi
    cv
    #
    co
    wcel
    @26
    @27
    @30
    @47
    co
    wcel
    @30
    @26
    @27
    @47
    co
    wcel
    w3o
    vz
    @46
    crab
    cmpt2
    wceq
    vi
    @45
    citv
    cfv
    wsbc
    vp
    @45
    cbs
    cfv
    wsbc
    vf
    cab
    cin
    #
    cin
    #
    cstrkgb
    vx
    vy
    vz
    vf
    vi
    vp
    df-trkg
    @49
    @44
    cstrkgb
    @44
    @48
    inss1
    cstrkgc
    cstrkgb
    inss2
    sstri
    eqsstri
    axtrkg.g
    sseldi
    @43
    @30
    @26
    @26
    cI
    co
    wcel
    @26
    @30
    wceq
    wi
    vy
    cP
    wral
    vx
    cP
    wral
    #
    @42
    @26
    @4
    @30
    cI
    co
    wcel
    vy
    vt
    cv
    #
    wral
    vx
    vs
    cv
    #
    wral
    va
    cP
    wrex
    vb
    cv
    @26
    @30
    cI
    co
    wcel
    vy
    @51
    wral
    vx
    @52
    wral
    vb
    cP
    wrex
    wi
    vt
    cP
    cpw
    #
    wral
    vs
    @53
    wral
    #
    @43
    cG
    cvv
    wcel
    @50
    @42
    @54
    w3a
    vx
    vy
    vz
    vv
    vu
    vt
    cP
    cG
    cI
    c.mi
    vs
    va
    vb
    axtrkg.p
    axtrkg.d
    axtrkg.i
    istrkgb
    simprbi
    simp2d
    syl
    wph
    cX
    cP
    wcel
    cY
    cP
    wcel
    cZ
    cP
    wcel
    @42
    @23
    wi
    axtgpasch.1
    axtgpasch.2
    axtgpasch.3
    @41
    @23
    @11
    cX
    @27
    cI
    co
    #
    wcel
    #
    @32
    wa
    #
    @35
    @19
    wa
    #
    va
    cP
    wrex
    #
    wi
    #
    vv
    cP
    wral
    vu
    cP
    wral
    @56
    @13
    cY
    @27
    cI
    co
    #
    wcel
    #
    wa
    #
    @21
    wi
    #
    vv
    cP
    wral
    vu
    cP
    wral
    vx
    vy
    vz
    cX
    cY
    cZ
    cP
    cP
    cP
    @26
    cX
    wceq
    #
    @40
    @60
    vu
    vv
    cP
    cP
    @65
    @33
    @57
    @39
    @59
    @65
    @29
    @56
    @32
    @65
    @28
    @55
    @11
    @26
    cX
    @27
    cI
    oveq1
    eleq2d
    anbi1d
    @65
    @38
    @58
    va
    cP
    @65
    @37
    @19
    @35
    @65
    @36
    @18
    @4
    @26
    cX
    @13
    cI
    oveq2
    eleq2d
    anbi2d
    rexbidv
    imbi12d
    2ralbidv
    @30
    cY
    wceq
    #
    @60
    @64
    vu
    vv
    cP
    cP
    @66
    @57
    @63
    @59
    @21
    @66
    @32
    @62
    @56
    @66
    @31
    @61
    @13
    @30
    cY
    @27
    cI
    oveq1
    eleq2d
    anbi2d
    @66
    @58
    @20
    va
    cP
    @66
    @35
    @17
    @19
    @66
    @34
    @16
    @4
    @30
    cY
    @11
    cI
    oveq2
    eleq2d
    anbi1d
    rexbidv
    imbi12d
    2ralbidv
    @27
    cZ
    wceq
    #
    @64
    @22
    vu
    vv
    cP
    cP
    @67
    @63
    @15
    @21
    @67
    @56
    @12
    @62
    @14
    @67
    @55
    @0
    @11
    @27
    cZ
    cX
    cI
    oveq2
    eleq2d
    @67
    @61
    @2
    @13
    @27
    cZ
    cY
    cI
    oveq2
    eleq2d
    anbi12d
    imbi1d
    2ralbidv
    rspc3v
    syl3anc
    mpd
    wph
    cU
    cP
    wcel
    cV
    cP
    wcel
    @23
    @25
    wi
    axtgpasch.4
    axtgpasch.5
    @22
    @25
    @1
    @14
    wa
    #
    @6
    @19
    wa
    #
    va
    cP
    wrex
    #
    wi
    vu
    vv
    cU
    cV
    cP
    cP
    @11
    cU
    wceq
    #
    @15
    @68
    @21
    @70
    @71
    @12
    @1
    @14
    @11
    cU
    @0
    eleq1
    anbi1d
    @71
    @20
    @69
    va
    cP
    @71
    @17
    @6
    @19
    @71
    @16
    @5
    @4
    @11
    cU
    cY
    cI
    oveq1
    eleq2d
    anbi1d
    rexbidv
    imbi12d
    @13
    cV
    wceq
    #
    @68
    @24
    @70
    @10
    @72
    @14
    @3
    @1
    @13
    cV
    @2
    eleq1
    anbi2d
    @72
    @69
    @9
    va
    cP
    @72
    @19
    @8
    @6
    @72
    @18
    @7
    @4
    @13
    cV
    cX
    cI
    oveq1
    eleq2d
    anbi2d
    rexbidv
    imbi12d
    rspc2v
    syl2anc
    mpd
    mp2and
end
