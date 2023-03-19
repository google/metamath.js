include "cims.mm"
include "cfv.mm"
include "cv.mm"
include "co.mm"
include "cmpt.mm"
include "crn.mm"
include "cr.mm"
include "clt.mm"
include "cinf.mm"
include "cmopn.mm"
include "eqid.mm"
include "wceq.mm"
include "oveq2.mm"
include "fveq2d.mm"
include "cbvmptv.mm"
include "rneqi.mm"
include "minvecolem7.mm"

theorem minveco
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cU: class U
  let cM: class M
  let cN: class N
  let cW: class W
  let cX: class X
  let cY: class Y
  let vj: setvar j
  let vn: setvar n
  let cF: class F
  let vk: setvar k
  let vw: setvar w
  let cJ: class J
  let cK: class K
  let cL: class L
  let vf: setvar f
  let cR: class R
  let cS: class S
  let cD: class D
  let cT: class T
  assume minveco.x: |- X = ( BaseSet ` U )
  assume minveco.m: |- M = ( -v ` U )
  assume minveco.n: |- N = ( normCV ` U )
  assume minveco.y: |- Y = ( BaseSet ` W )
  assume minveco.u: |- ( ph -> U e. CPreHilOLD )
  assume minveco.w: |- ( ph -> W e. ( ( SubSp ` U ) i^i CBan ) )
  assume minveco.a: |- ( ph -> A e. X )

  disjoint x y
  disjoint M x
  disjoint M y
  disjoint N x
  disjoint N y
  disjoint ph x
  disjoint ph y
  disjoint A x
  disjoint A y
  disjoint U x
  disjoint U y
  disjoint W x
  disjoint W y
  disjoint X x
  disjoint Y x
  disjoint Y y
  disjoint j n
  disjoint j x
  disjoint j y
  disjoint F j
  disjoint n x
  disjoint n y
  disjoint F n
  disjoint F x
  disjoint F y
  disjoint k n
  disjoint k w
  disjoint k x
  disjoint k y
  disjoint J k
  disjoint n w
  disjoint J n
  disjoint w x
  disjoint w y
  disjoint J w
  disjoint J x
  disjoint J y
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
  disjoint N f
  disjoint N j
  disjoint N w
  disjoint f k
  disjoint f n
  disjoint f ph
  disjoint j k
  disjoint j ph
  disjoint k ph
  disjoint n ph
  disjoint ph w
  disjoint R w
  disjoint R x
  disjoint S f
  disjoint S k
  disjoint S n
  disjoint S w
  disjoint S x
  disjoint S y
  disjoint A f
  disjoint A j
  disjoint A k
  disjoint A n
  disjoint A w
  disjoint D f
  disjoint D j
  disjoint D k
  disjoint D n
  disjoint D w
  disjoint D x
  disjoint D y
  disjoint U w
  disjoint W w
  disjoint T n
  disjoint X j
  disjoint X k
  disjoint X n
  disjoint X w
  disjoint Y f
  disjoint Y j
  disjoint Y k
  disjoint Y n
  disjoint Y w
  assert |- ( ph -> E! x e. Y A. y e. Y ( N ` ( A M x ) ) <_ ( N ` ( A M y ) ) )

  proof
    wph
    vx
    vy
    cA
    cU
    cims
    cfv
    #
    vj
    cY
    cA
    vj
    cv
    #
    cM
    co
    #
    cN
    cfv
    #
    cmpt
    #
    crn
    #
    @5
    cr
    clt
    cinf
    #
    cU
    @0
    cmopn
    cfv
    #
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
    @0
    eqid
    @7
    eqid
    @4
    vy
    cY
    cA
    vy
    cv
    #
    cM
    co
    #
    cN
    cfv
    #
    cmpt
    vj
    vy
    cY
    @3
    @10
    @1
    @8
    wceq
    @2
    @9
    cN
    @1
    @8
    cA
    cM
    oveq2
    fveq2d
    cbvmptv
    rneqi
    @6
    eqid
    minvecolem7
end
