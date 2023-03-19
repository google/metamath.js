include "cv.mm"
include "co.mm"
include "wcel.mm"
include "wral.mm"
include "wrex.mm"
include "3expb.mm"
include "ralrimivva.mm"
include "wceq.mm"
include "wa.mm"
include "simplr.mm"
include "simpll.mm"
include "simpr.mm"
include "oveq12d.mm"
include "eleq12d.mm"
include "cbvraldva.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "axtgcont1.mm"
include "mpd.mm"

theorem axtgcont
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vv: setvar v
  let vu: setvar u
  let cA: class A
  let cP: class P
  let cS: class S
  let cT: class T
  let cG: class G
  let cI: class I
  let c.mi: class .-
  let vb: setvar b
  let vf: setvar f
  let vi: setvar i
  let vp: setvar p
  let vz: setvar z
  let va: setvar a
  let vc: setvar c
  let cB: class B
  let cC: class C
  let vs: setvar s
  let vt: setvar t
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
  assume axtgcont.3: |- ( ph -> A e. P )
  assume axtgcont.4: |- ( ( ph /\ u e. S /\ v e. T ) -> u e. ( A I v ) )

  disjoint u v
  disjoint ph u
  disjoint ph v
  disjoint S u
  disjoint S v
  disjoint T u
  disjoint T v
  disjoint u x
  disjoint u y
  disjoint A u
  disjoint v x
  disjoint v y
  disjoint A v
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint x y
  disjoint b v
  disjoint A b
  disjoint A v
  disjoint b u
  disjoint b x
  disjoint b y
  disjoint I b
  disjoint u v
  disjoint u x
  disjoint u y
  disjoint I u
  disjoint v x
  disjoint v y
  disjoint I v
  disjoint I x
  disjoint I y
  disjoint P b
  disjoint P u
  disjoint P v
  disjoint P x
  disjoint P y
  disjoint S b
  disjoint S x
  disjoint T b
  disjoint T x
  disjoint T y
  disjoint .- b
  disjoint .- u
  disjoint .- v
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
  disjoint a b
  disjoint a c
  disjoint a v
  disjoint a z
  disjoint A a
  disjoint b c
  disjoint b z
  disjoint c v
  disjoint c z
  disjoint A c
  disjoint v z
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
  disjoint I a
  disjoint b s
  disjoint b t
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
  disjoint u z
  disjoint I z
  disjoint P a
  disjoint P c
  disjoint P s
  disjoint P t
  disjoint P z
  disjoint S a
  disjoint S s
  disjoint S t
  disjoint T a
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
  disjoint .- a
  disjoint .- c
  disjoint .- z
  assert |- ( ph -> E. b e. P A. x e. S A. y e. T b e. ( x I y ) )

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
    #
    wcel
    #
    vy
    cT
    wral
    #
    vx
    cS
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
    vy
    cT
    wral
    vx
    cS
    wral
    vb
    cP
    wrex
    wph
    cA
    cP
    wcel
    vu
    cv
    #
    cA
    vv
    cv
    #
    cI
    co
    #
    wcel
    #
    vv
    cT
    wral
    #
    vu
    cS
    wral
    #
    @7
    axtgcont.3
    wph
    @11
    vu
    vv
    cS
    cT
    wph
    @8
    cS
    wcel
    @9
    cT
    wcel
    @11
    axtgcont.4
    3expb
    ralrimivva
    @6
    @13
    va
    cA
    cP
    @1
    cA
    wceq
    #
    @5
    @12
    vx
    vu
    cS
    @14
    @0
    @8
    wceq
    #
    wa
    #
    @4
    @11
    vy
    vv
    cT
    @16
    @2
    @9
    wceq
    #
    wa
    #
    @0
    @8
    @3
    @10
    @14
    @15
    @17
    simplr
    @18
    @1
    cA
    @2
    @9
    cI
    @14
    @15
    @17
    simpll
    @16
    @17
    simpr
    oveq12d
    eleq12d
    cbvraldva
    cbvraldva
    rspcev
    syl2anc
    wph
    vx
    vy
    cP
    cS
    cT
    cG
    cI
    c.mi
    va
    vb
    axtrkg.p
    axtrkg.d
    axtrkg.i
    axtrkg.g
    axtgcont.1
    axtgcont.2
    axtgcont1
    mpd
end
