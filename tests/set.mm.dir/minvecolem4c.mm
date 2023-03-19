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
include "minvecolem1.mm"
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

theorem minvecolem4c
  let wph: wff ph
  let vy: setvar y
  let cA: class A
  let cD: class D
  let cR: class R
  let cS: class S
  let cU: class U
  let vn: setvar n
  let cF: class F
  let cJ: class J
  let cM: class M
  let cN: class N
  let cW: class W
  let cX: class X
  let cY: class Y
  let vj: setvar j
  let vx: setvar x
  let vk: setvar k
  let vw: setvar w
  let cK: class K
  let cL: class L
  let vf: setvar f
  let cT: class T
  assume minveco.x: |- X = ( BaseSet ` U )
  assume minveco.m: |- M = ( -v ` U )
  assume minveco.n: |- N = ( normCV ` U )
  assume minveco.y: |- Y = ( BaseSet ` W )
  assume minveco.u: |- ( ph -> U e. CPreHilOLD )
  assume minveco.w: |- ( ph -> W e. ( ( SubSp ` U ) i^i CBan ) )
  assume minveco.a: |- ( ph -> A e. X )
  assume minveco.d: |- D = ( IndMet ` U )
  assume minveco.j: |- J = ( MetOpen ` D )
  assume minveco.r: |- R = ran ( y e. Y |-> ( N ` ( A M y ) ) )
  assume minveco.s: |- S = inf ( R , RR , < )
  assume minveco.f: |- ( ph -> F : NN --> Y )
  assume minveco.1: |- ( ( ph /\ n e. NN ) -> ( ( A D ( F ` n ) ) ^ 2 ) <_ ( ( S ^ 2 ) + ( 1 / n ) ) )

  disjoint n y
  disjoint F n
  disjoint F y
  disjoint J n
  disjoint J y
  disjoint M y
  disjoint N y
  disjoint n ph
  disjoint ph y
  disjoint S n
  disjoint S y
  disjoint A n
  disjoint A y
  disjoint D n
  disjoint D y
  disjoint U y
  disjoint W y
  disjoint X n
  disjoint Y n
  disjoint Y y
  disjoint j n
  disjoint j x
  disjoint j y
  disjoint F j
  disjoint n x
  disjoint x y
  disjoint F x
  disjoint k n
  disjoint k w
  disjoint k x
  disjoint k y
  disjoint J k
  disjoint n w
  disjoint w x
  disjoint w y
  disjoint J w
  disjoint J x
  disjoint K y
  disjoint L y
  disjoint f j
  disjoint f w
  disjoint f x
  disjoint f y
  disjoint M f
  disjoint j w
  disjoint M j
  disjoint M w
  disjoint M x
  disjoint N f
  disjoint N j
  disjoint N w
  disjoint N x
  disjoint f k
  disjoint f n
  disjoint f ph
  disjoint j k
  disjoint j ph
  disjoint k ph
  disjoint ph w
  disjoint ph x
  disjoint R w
  disjoint R x
  disjoint S f
  disjoint S k
  disjoint S w
  disjoint S x
  disjoint A f
  disjoint A j
  disjoint A k
  disjoint A w
  disjoint A x
  disjoint D f
  disjoint D j
  disjoint D k
  disjoint D w
  disjoint D x
  disjoint U w
  disjoint U x
  disjoint W w
  disjoint W x
  disjoint T n
  disjoint X j
  disjoint X k
  disjoint X w
  disjoint X x
  disjoint Y f
  disjoint Y j
  disjoint Y k
  disjoint Y w
  disjoint Y x
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
    minveco.s
    wph
    cR
    cr
    wss
    #
    cR
    c0
    wne
    #
    vx
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
    vx
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
    cD
    cR
    cU
    cJ
    cM
    cN
    cW
    cX
    cY
    minveco.x
    minveco.m
    minveco.n
    minveco.y
    minveco.u
    minveco.w
    minveco.a
    minveco.d
    minveco.j
    minveco.r
    minvecolem1
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
    vx
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
    vx
    vw
    cR
    infrecl
    syl3anc
    syl5eqel
end
