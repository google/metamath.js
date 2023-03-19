include "cv.mm"
include "co.mm"
include "wcel.mm"
include "wceq.mm"
include "wa.mm"
include "wrex.mm"
include "wral.mm"
include "cstrkgcb.mm"
include "cstrkg.mm"
include "cstrkgc.mm"
include "cstrkgb.mm"
include "cin.mm"
include "clng.mm"
include "cfv.mm"
include "csn.mm"
include "cdif.mm"
include "w3o.mm"
include "crab.mm"
include "cmpt2.mm"
include "citv.mm"
include "wsbc.mm"
include "cbs.mm"
include "cab.mm"
include "df-trkg.mm"
include "inss2.mm"
include "inss1.mm"
include "sstri.mm"
include "eqsstri.mm"
include "sseldi.mm"
include "wne.mm"
include "w3a.mm"
include "wi.mm"
include "cvv.mm"
include "istrkgcb.mm"
include "simprbi.mm"
include "simprd.mm"
include "syl.mm"
include "oveq1.mm"
include "eleq2d.mm"
include "anbi1d.mm"
include "rexbidv.mm"
include "2ralbidv.mm"
include "eleq1.mm"
include "eqeq1d.mm"
include "anbi12d.mm"
include "rspc2v.mm"
include "syl2anc.mm"
include "mpd.mm"
include "eqeq2d.mm"
include "anbi2d.mm"
include "oveq2.mm"

theorem axtgsegcon
  let wph: wff ph
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cP: class P
  let cG: class G
  let cI: class I
  let c.mi: class .-
  let cX: class X
  let cY: class Y
  let vf: setvar f
  let vi: setvar i
  let vp: setvar p
  let vx: setvar x
  let vy: setvar y
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vv: setvar v
  let cC: class C
  let vs: setvar s
  let vt: setvar t
  let vu: setvar u
  let cS: class S
  let cT: class T
  let cU: class U
  let cZ: class Z
  let cV: class V
  assume axtrkg.p: |- P = ( Base ` G )
  assume axtrkg.d: |- .- = ( dist ` G )
  assume axtrkg.i: |- I = ( Itv ` G )
  assume axtrkg.g: |- ( ph -> G e. TarskiG )
  assume axtgsegcon.1: |- ( ph -> X e. P )
  assume axtgsegcon.2: |- ( ph -> Y e. P )
  assume axtgsegcon.3: |- ( ph -> A e. P )
  assume axtgsegcon.4: |- ( ph -> B e. P )

  disjoint A z
  disjoint B z
  disjoint I z
  disjoint P z
  disjoint X z
  disjoint Y z
  disjoint .- z
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
  disjoint B b
  disjoint B c
  disjoint B v
  disjoint C c
  disjoint C v
  disjoint a s
  disjoint a t
  disjoint a u
  disjoint a x
  disjoint a y
  disjoint I a
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
  disjoint P a
  disjoint P b
  disjoint P c
  disjoint P s
  disjoint P t
  disjoint P u
  disjoint P v
  disjoint P x
  disjoint P y
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
  disjoint Y a
  disjoint Y b
  disjoint Y c
  disjoint Y u
  disjoint Y v
  disjoint Y y
  disjoint Z a
  disjoint Z b
  disjoint Z c
  disjoint Z u
  disjoint Z v
  disjoint Z z
  disjoint V a
  disjoint V b
  disjoint V v
  disjoint .- a
  disjoint .- b
  disjoint .- c
  disjoint .- u
  disjoint .- v
  disjoint .- x
  disjoint .- y
  assert |- ( ph -> E. z e. P ( Y e. ( X I z ) /\ ( Y .- z ) = ( A .- B ) ) )

  proof
    wph
    cY
    cX
    vz
    cv
    #
    cI
    co
    #
    wcel
    #
    cY
    @0
    c.mi
    co
    #
    va
    cv
    #
    vb
    cv
    #
    c.mi
    co
    #
    wceq
    #
    wa
    #
    vz
    cP
    wrex
    #
    vb
    cP
    wral
    va
    cP
    wral
    #
    @2
    @3
    cA
    cB
    c.mi
    co
    #
    wceq
    #
    wa
    #
    vz
    cP
    wrex
    #
    wph
    vy
    cv
    #
    vx
    cv
    #
    @0
    cI
    co
    #
    wcel
    #
    @15
    @0
    c.mi
    co
    #
    @6
    wceq
    #
    wa
    #
    vz
    cP
    wrex
    #
    vb
    cP
    wral
    va
    cP
    wral
    #
    vy
    cP
    wral
    vx
    cP
    wral
    #
    @10
    wph
    cG
    cstrkgcb
    wcel
    #
    @24
    wph
    cstrkg
    cstrkgcb
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
    @28
    @16
    csn
    cdif
    @0
    @16
    @15
    vi
    cv
    #
    co
    wcel
    @16
    @0
    @15
    @29
    co
    wcel
    @15
    @16
    @0
    @29
    co
    wcel
    w3o
    vz
    @28
    crab
    cmpt2
    wceq
    vi
    @27
    citv
    cfv
    wsbc
    vp
    @27
    cbs
    cfv
    wsbc
    vf
    cab
    #
    cin
    #
    cin
    #
    cstrkgcb
    vx
    vy
    vz
    vf
    vi
    vp
    df-trkg
    @32
    @31
    cstrkgcb
    @26
    @31
    inss2
    cstrkgcb
    @30
    inss1
    sstri
    eqsstri
    axtrkg.g
    sseldi
    @25
    @16
    @15
    wne
    @18
    @5
    @4
    vc
    cv
    #
    cI
    co
    wcel
    w3a
    @16
    @15
    c.mi
    co
    @6
    wceq
    @19
    @5
    @33
    c.mi
    co
    wceq
    wa
    @16
    vu
    cv
    #
    c.mi
    co
    @4
    vv
    cv
    #
    c.mi
    co
    wceq
    @15
    @34
    c.mi
    co
    @5
    @35
    c.mi
    co
    wceq
    wa
    wa
    wa
    @0
    @34
    c.mi
    co
    @33
    @35
    c.mi
    co
    wceq
    wi
    vv
    cP
    wral
    vc
    cP
    wral
    vb
    cP
    wral
    va
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
    @24
    @25
    cG
    cvv
    wcel
    @36
    @24
    wa
    vx
    vy
    vz
    vv
    vu
    cP
    cG
    cI
    c.mi
    va
    vb
    vc
    axtrkg.p
    axtrkg.d
    axtrkg.i
    istrkgcb
    simprbi
    simprd
    syl
    wph
    cX
    cP
    wcel
    cY
    cP
    wcel
    @24
    @10
    wi
    axtgsegcon.1
    axtgsegcon.2
    @23
    @10
    @15
    @1
    wcel
    #
    @20
    wa
    #
    vz
    cP
    wrex
    #
    vb
    cP
    wral
    va
    cP
    wral
    vx
    vy
    cX
    cY
    cP
    cP
    @16
    cX
    wceq
    #
    @22
    @39
    va
    vb
    cP
    cP
    @40
    @21
    @38
    vz
    cP
    @40
    @18
    @37
    @20
    @40
    @17
    @1
    @15
    @16
    cX
    @0
    cI
    oveq1
    eleq2d
    anbi1d
    rexbidv
    2ralbidv
    @15
    cY
    wceq
    #
    @39
    @9
    va
    vb
    cP
    cP
    @41
    @38
    @8
    vz
    cP
    @41
    @37
    @2
    @20
    @7
    @15
    cY
    @1
    eleq1
    @41
    @19
    @3
    @6
    @15
    cY
    @0
    c.mi
    oveq1
    eqeq1d
    anbi12d
    rexbidv
    2ralbidv
    rspc2v
    syl2anc
    mpd
    wph
    cA
    cP
    wcel
    cB
    cP
    wcel
    @10
    @14
    wi
    axtgsegcon.3
    axtgsegcon.4
    @9
    @14
    @2
    @3
    cA
    @5
    c.mi
    co
    #
    wceq
    #
    wa
    #
    vz
    cP
    wrex
    va
    vb
    cA
    cB
    cP
    cP
    @4
    cA
    wceq
    #
    @8
    @44
    vz
    cP
    @45
    @7
    @43
    @2
    @45
    @6
    @42
    @3
    @4
    cA
    @5
    c.mi
    oveq1
    eqeq2d
    anbi2d
    rexbidv
    @5
    cB
    wceq
    #
    @44
    @13
    vz
    cP
    @46
    @43
    @12
    @2
    @46
    @42
    @11
    @3
    @5
    cB
    cA
    c.mi
    oveq2
    eqeq2d
    anbi2d
    rexbidv
    rspc2v
    syl2anc
    mpd
end
