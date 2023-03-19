include "cv.mm"
include "co.mm"
include "wcel.mm"
include "wral.mm"
include "wrex.mm"
include "wi.mm"
include "cpw.mm"
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
include "wa.mm"
include "cvv.mm"
include "w3a.mm"
include "istrkgb.mm"
include "simprbi.mm"
include "simp3d.mm"
include "syl.mm"
include "wss.mm"
include "wb.mm"
include "fvex.mm"
include "eqeltri.mm"
include "ssex.mm"
include "elpwg.mm"
include "3syl.mm"
include "mpbird.mm"
include "raleq.mm"
include "rexbidv.mm"
include "imbi12d.mm"
include "rexralbidv.mm"
include "rspc2v.mm"
include "syl2anc.mm"
include "mpd.mm"

theorem axtgcont1
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cP: class P
  let cS: class S
  let cT: class T
  let cG: class G
  let cI: class I
  let c.mi: class .-
  let va: setvar a
  let vb: setvar b
  let vf: setvar f
  let vi: setvar i
  let vp: setvar p
  let vz: setvar z
  let vc: setvar c
  let vv: setvar v
  let cA: class A
  let cB: class B
  let cC: class C
  let vs: setvar s
  let vt: setvar t
  let vu: setvar u
  let cU: class U
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let cV: class V
  assume axtrkg.p: |- P = ( Base ` G )
  assume axtrkg.d: |- .- = ( dist ` G )
  assume axtrkg.i: |- I = ( Itv ` G )
  assume axtrkg.g: |- ( ph -> G e. TarskiG )
  assume axtgcont.1: |- ( ph -> S C_ P )
  assume axtgcont.2: |- ( ph -> T C_ P )

  disjoint x y
  disjoint a b
  disjoint a x
  disjoint a y
  disjoint I a
  disjoint b x
  disjoint b y
  disjoint I b
  disjoint I x
  disjoint I y
  disjoint P a
  disjoint P b
  disjoint P x
  disjoint P y
  disjoint S a
  disjoint S b
  disjoint S x
  disjoint T a
  disjoint T b
  disjoint T x
  disjoint T y
  disjoint .- a
  disjoint .- b
  disjoint .- x
  disjoint .- y
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
  disjoint x z
  disjoint y z
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
  disjoint b s
  disjoint b t
  disjoint b u
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
  disjoint I z
  disjoint P c
  disjoint P s
  disjoint P t
  disjoint P u
  disjoint P v
  disjoint P z
  disjoint S s
  disjoint S t
  disjoint T t
  disjoint U a
  disjoint U b
  disjoint U c
  disjoint U u
  disjoint U v
  disjoint X a
  disjoint X b
  disjoint X c
  disjoint X u
  disjoint X v
  disjoint X x
  disjoint X y
  disjoint X z
  disjoint Y a
  disjoint Y b
  disjoint Y c
  disjoint Y u
  disjoint Y v
  disjoint Y y
  disjoint Y z
  disjoint Z a
  disjoint Z b
  disjoint Z c
  disjoint Z u
  disjoint Z v
  disjoint Z z
  disjoint V a
  disjoint V b
  disjoint V v
  disjoint .- c
  disjoint .- u
  disjoint .- v
  disjoint .- z
  assert |- ( ph -> ( E. a e. P A. x e. S A. y e. T x e. ( a I y ) -> E. b e. P A. x e. S A. y e. T b e. ( x I y ) ) )

  proof
    wph
    vx
    cv
    #
    va
    cv
    #
    vy
    cv
    #
    cI
    co
    wcel
    #
    vy
    vt
    cv
    #
    wral
    #
    vx
    vs
    cv
    #
    wral
    #
    va
    cP
    wrex
    #
    vb
    cv
    @0
    @2
    cI
    co
    wcel
    #
    vy
    @4
    wral
    #
    vx
    @6
    wral
    #
    vb
    cP
    wrex
    #
    wi
    #
    vt
    cP
    cpw
    #
    wral
    vs
    @14
    wral
    #
    @3
    vy
    cT
    wral
    #
    vx
    cS
    wral
    va
    cP
    wrex
    #
    @9
    vy
    cT
    wral
    #
    vx
    cS
    wral
    vb
    cP
    wrex
    #
    wi
    #
    wph
    cG
    cstrkgb
    wcel
    #
    @15
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
    @24
    @0
    csn
    cdif
    vz
    cv
    #
    @0
    @2
    vi
    cv
    #
    co
    wcel
    @0
    @25
    @2
    @26
    co
    wcel
    @2
    @0
    @25
    @26
    co
    wcel
    w3o
    vz
    @24
    crab
    cmpt2
    wceq
    vi
    @23
    citv
    cfv
    wsbc
    vp
    @23
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
    @28
    @22
    cstrkgb
    @22
    @27
    inss1
    cstrkgc
    cstrkgb
    inss2
    sstri
    eqsstri
    axtrkg.g
    sseldi
    @21
    @2
    @0
    @0
    cI
    co
    wcel
    @0
    @2
    wceq
    wi
    vy
    cP
    wral
    vx
    cP
    wral
    #
    vu
    cv
    #
    @0
    @25
    cI
    co
    wcel
    vv
    cv
    #
    @2
    @25
    cI
    co
    wcel
    wa
    @1
    @30
    @2
    cI
    co
    wcel
    @1
    @31
    @0
    cI
    co
    wcel
    wa
    va
    cP
    wrex
    wi
    vv
    cP
    wral
    vu
    cP
    wral
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
    @15
    @21
    cG
    cvv
    wcel
    @29
    @32
    @15
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
    simp3d
    syl
    wph
    cS
    @14
    wcel
    #
    cT
    @14
    wcel
    #
    @15
    @20
    wi
    wph
    @33
    cS
    cP
    wss
    #
    axtgcont.1
    wph
    @35
    cS
    cvv
    wcel
    @33
    @35
    wb
    axtgcont.1
    cS
    cP
    cP
    cG
    cbs
    cfv
    cvv
    axtrkg.p
    cG
    cbs
    fvex
    eqeltri
    #
    ssex
    cS
    cP
    cvv
    elpwg
    3syl
    mpbird
    wph
    @34
    cT
    cP
    wss
    #
    axtgcont.2
    wph
    @37
    cT
    cvv
    wcel
    @34
    @37
    wb
    axtgcont.2
    cT
    cP
    @36
    ssex
    cT
    cP
    cvv
    elpwg
    3syl
    mpbird
    @13
    @20
    @5
    vx
    cS
    wral
    #
    va
    cP
    wrex
    #
    @10
    vx
    cS
    wral
    #
    vb
    cP
    wrex
    #
    wi
    vs
    vt
    cS
    cT
    @14
    @14
    @6
    cS
    wceq
    #
    @8
    @39
    @12
    @41
    @42
    @7
    @38
    va
    cP
    @5
    vx
    @6
    cS
    raleq
    rexbidv
    @42
    @11
    @40
    vb
    cP
    @10
    vx
    @6
    cS
    raleq
    rexbidv
    imbi12d
    @4
    cT
    wceq
    #
    @39
    @17
    @41
    @19
    @43
    @5
    @16
    va
    vx
    cP
    cS
    @3
    vy
    @4
    cT
    raleq
    rexralbidv
    @43
    @10
    @18
    vb
    vx
    cP
    cS
    @9
    vy
    @4
    cT
    raleq
    rexralbidv
    imbi12d
    rspc2v
    syl2anc
    mpd
end
