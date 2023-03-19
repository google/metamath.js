include "clss.mm"
include "cfv.mm"
include "wcel.mm"
include "wss.mm"
include "eqid.mm"
include "lssss.mm"
include "syl.mm"
include "cfg.mm"
include "co.mm"
include "cflim.mm"
include "cin.mm"
include "inss2.mm"
include "minveclem4a.mm"
include "sseldi.mm"
include "sseldd.mm"

theorem minveclem4b
  let wph: wff ph
  let vy: setvar y
  let cA: class A
  let cD: class D
  let cP: class P
  let cR: class R
  let cS: class S
  let cU: class U
  let cF: class F
  let cJ: class J
  let c.mi: class .-
  let cN: class N
  let cX: class X
  let cY: class Y
  let vr: setvar r
  let vj: setvar j
  let vw: setvar w
  let vx: setvar x
  let vs: setvar s
  let vt: setvar t
  let vu: setvar u
  let vv: setvar v
  let vz: setvar z
  let cK: class K
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
  assume minvec.d: |- D = ( ( dist ` U ) |` ( X X. X ) )
  assume minvec.f: |- F = ran ( r e. RR+ |-> { y e. Y | ( ( A D y ) ^ 2 ) <_ ( ( S ^ 2 ) + r ) } )
  assume minvec.p: |- P = U. ( J fLim ( X filGen F ) )

  disjoint .- y
  disjoint r y
  disjoint A r
  disjoint A y
  disjoint J r
  disjoint J y
  disjoint P y
  disjoint F y
  disjoint N y
  disjoint ph r
  disjoint ph y
  disjoint R y
  disjoint U y
  disjoint X r
  disjoint X y
  disjoint Y r
  disjoint Y y
  disjoint D r
  disjoint D y
  disjoint S r
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
  disjoint r z
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
  disjoint J w
  disjoint J x
  disjoint P x
  disjoint F s
  disjoint F t
  disjoint F u
  disjoint F v
  disjoint F w
  disjoint F x
  disjoint K y
  disjoint N j
  disjoint N w
  disjoint N x
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
  disjoint X w
  disjoint X x
  disjoint Y j
  disjoint Y s
  disjoint Y t
  disjoint Y u
  disjoint Y v
  disjoint Y w
  disjoint Y x
  disjoint Y z
  disjoint D s
  disjoint D t
  disjoint D u
  disjoint D v
  disjoint D w
  disjoint D x
  disjoint D z
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
  assert |- ( ph -> P e. X )

  proof
    wph
    cY
    cX
    cP
    wph
    cY
    cU
    clss
    cfv
    #
    wcel
    cY
    cX
    wss
    minvec.y
    @0
    cY
    cX
    cU
    minvec.x
    @0
    eqid
    lssss
    syl
    wph
    cJ
    cX
    cF
    cfg
    co
    cflim
    co
    #
    cY
    cin
    cY
    cP
    @1
    cY
    inss2
    wph
    vy
    cA
    cD
    cP
    cR
    cS
    cU
    cF
    cJ
    c.mi
    cN
    cX
    cY
    vr
    minvec.x
    minvec.m
    minvec.n
    minvec.u
    minvec.y
    minvec.w
    minvec.a
    minvec.j
    minvec.r
    minvec.s
    minvec.d
    minvec.f
    minvec.p
    minveclem4a
    sseldi
    sseldd
end
