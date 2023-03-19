include "cr.mm"
include "clt.mm"
include "cinf.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "wrex.mm"
include "wcel.mm"
include "cc0.mm"
include "minveclem1.mm"
include "simp1d.mm"
include "simp2d.mm"
include "0re.mm"
include "simp3d.mm"
include "wceq.mm"
include "breq1.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "sylancr.mm"
include "infrecl.mm"
include "syl3anc.mm"
include "syl5eqel.mm"

theorem minveclem4c
  let wph: wff ph
  let vy: setvar y
  let cA: class A
  let cR: class R
  let cS: class S
  let cU: class U
  let cJ: class J
  let c.mi: class .-
  let cN: class N
  let cX: class X
  let cY: class Y
  let vj: setvar j
  let vw: setvar w
  let vx: setvar x
  let vr: setvar r
  let vs: setvar s
  let vt: setvar t
  let vu: setvar u
  let vv: setvar v
  let vz: setvar z
  let cP: class P
  let cF: class F
  let cK: class K
  let cD: class D
  let cT: class T
  let cL: class L
  assume minvec.x: |- X = ( Base ` U )
  assume minvec.m: |- .- = ( -g ` U )
  assume minvec.n: |- N = ( norm ` U )
  assume minvec.u: |- ( ph -> U e. CPreHil )
  assume minvec.y: |- ( ph -> Y e. ( LSubSp ` U ) )
  assume minvec.w: |- ( ph -> ( U |`s Y ) e. CMetSp )
  assume minvec.a: |- ( ph -> A e. X )
  assume minvec.j: |- J = ( TopOpen ` U )
  assume minvec.r: |- R = ran ( y e. Y |-> ( N ` ( A .- y ) ) )
  assume minvec.s: |- S = inf ( R , RR , < )

  disjoint .- y
  disjoint A y
  disjoint J y
  disjoint N y
  disjoint ph y
  disjoint R y
  disjoint U y
  disjoint X y
  disjoint Y y
  disjoint S y
  disjoint j w
  disjoint j x
  disjoint j y
  disjoint .- j
  disjoint w x
  disjoint w y
  disjoint .- w
  disjoint x y
  disjoint .- x
  disjoint j r
  disjoint j s
  disjoint j t
  disjoint j u
  disjoint j v
  disjoint j z
  disjoint A j
  disjoint r s
  disjoint r t
  disjoint r u
  disjoint r v
  disjoint r w
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint A r
  disjoint s t
  disjoint s u
  disjoint s v
  disjoint s w
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint A s
  disjoint t u
  disjoint t v
  disjoint t w
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint A t
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint A u
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint A v
  disjoint w z
  disjoint A w
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A z
  disjoint J r
  disjoint J w
  disjoint J x
  disjoint P x
  disjoint P y
  disjoint F s
  disjoint F t
  disjoint F u
  disjoint F v
  disjoint F w
  disjoint F x
  disjoint F y
  disjoint K y
  disjoint N j
  disjoint N w
  disjoint N x
  disjoint ph r
  disjoint ph s
  disjoint ph t
  disjoint ph u
  disjoint ph v
  disjoint ph w
  disjoint ph x
  disjoint R w
  disjoint R x
  disjoint U w
  disjoint U x
  disjoint X r
  disjoint X w
  disjoint X x
  disjoint Y j
  disjoint Y r
  disjoint Y s
  disjoint Y t
  disjoint Y u
  disjoint Y v
  disjoint Y w
  disjoint Y x
  disjoint Y z
  disjoint D r
  disjoint D s
  disjoint D t
  disjoint D u
  disjoint D v
  disjoint D w
  disjoint D x
  disjoint D y
  disjoint D z
  disjoint S r
  disjoint S s
  disjoint S t
  disjoint S u
  disjoint S v
  disjoint S w
  disjoint S x
  disjoint S z
  disjoint T r
  disjoint T y
  disjoint L y
  assert |- ( ph -> S e. RR )

  proof
    wph
    cS
    cR
    cr
    clt
    cinf
    #
    cr
    minvec.s
    wph
    cR
    cr
    wss
    #
    cR
    c0
    wne
    #
    vy
    cv
    #
    vw
    cv
    #
    cle
    wbr
    #
    vw
    cR
    wral
    #
    vy
    cr
    wrex
    #
    @0
    cr
    wcel
    wph
    @1
    @2
    cc0
    @4
    cle
    wbr
    #
    vw
    cR
    wral
    #
    wph
    vy
    vw
    cA
    cR
    cU
    cJ
    c.mi
    cN
    cX
    cY
    minvec.x
    minvec.m
    minvec.n
    minvec.u
    minvec.y
    minvec.w
    minvec.a
    minvec.j
    minvec.r
    minveclem1
    #
    simp1d
    wph
    @1
    @2
    @9
    @10
    simp2d
    wph
    cc0
    cr
    wcel
    @9
    @7
    0re
    wph
    @1
    @2
    @9
    @10
    simp3d
    @6
    @9
    vy
    cc0
    cr
    @3
    cc0
    wceq
    @5
    @8
    vw
    cR
    @3
    cc0
    @4
    cle
    breq1
    ralbidv
    rspcev
    sylancr
    vy
    vw
    cR
    infrecl
    syl3anc
    syl5eqel
end
