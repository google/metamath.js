include "c0g.mm"
include "cfv.mm"
include "wne.mm"
include "wceq.mm"
include "wa.mm"
include "chlt.mm"
include "wcel.mm"
include "adantr.mm"
include "csn.mm"
include "cdif.mm"
include "simpr.mm"
include "lcfrlem33.mm"
include "lcfrlem32.mm"
include "pm2.61dane.mm"

theorem lcfrlem34
  let wph: wff ph
  let vx: setvar x
  let vw: setvar w
  let vv: setvar v
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let c.pl: class .+
  let cQ: class Q
  let cR: class R
  let cS: class S
  let c.x: class .x.
  let cU: class U
  let vk: setvar k
  let cF: class F
  let cH: class H
  let cI: class I
  let cJ: class J
  let cK: class K
  let cL: class L
  let c.mi: class .-
  let cN: class N
  let c.pe: class ._|_
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  let vf: setvar f
  assume lcfrlem17.h: |- H = ( LHyp ` K )
  assume lcfrlem17.o: |- ._|_ = ( ( ocH ` K ) ` W )
  assume lcfrlem17.u: |- U = ( ( DVecH ` K ) ` W )
  assume lcfrlem17.v: |- V = ( Base ` U )
  assume lcfrlem17.p: |- .+ = ( +g ` U )
  assume lcfrlem17.z: |- .0. = ( 0g ` U )
  assume lcfrlem17.n: |- N = ( LSpan ` U )
  assume lcfrlem17.a: |- A = ( LSAtoms ` U )
  assume lcfrlem17.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume lcfrlem17.x: |- ( ph -> X e. ( V \ { .0. } ) )
  assume lcfrlem17.y: |- ( ph -> Y e. ( V \ { .0. } ) )
  assume lcfrlem17.ne: |- ( ph -> ( N ` { X } ) =/= ( N ` { Y } ) )
  assume lcfrlem22.b: |- B = ( ( N ` { X , Y } ) i^i ( ._|_ ` { ( X .+ Y ) } ) )
  assume lcfrlem24.t: |- .x. = ( .s ` U )
  assume lcfrlem24.s: |- S = ( Scalar ` U )
  assume lcfrlem24.q: |- Q = ( 0g ` S )
  assume lcfrlem24.r: |- R = ( Base ` S )
  assume lcfrlem24.j: |- J = ( x e. ( V \ { .0. } ) |-> ( v e. V |-> ( iota_ k e. R E. w e. ( ._|_ ` { x } ) v = ( w .+ ( k .x. x ) ) ) ) )
  assume lcfrlem24.ib: |- ( ph -> I e. B )
  assume lcfrlem24.l: |- L = ( LKer ` U )
  assume lcfrlem25.d: |- D = ( LDual ` U )
  assume lcfrlem28.jn: |- ( ph -> ( ( J ` Y ) ` I ) =/= Q )
  assume lcfrlem29.i: |- F = ( invr ` S )
  assume lcfrlem30.m: |- .- = ( -g ` D )
  assume lcfrlem30.c: |- C = ( ( J ` X ) .- ( ( ( F ` ( ( J ` Y ) ` I ) ) ( .r ` S ) ( ( J ` X ) ` I ) ) ( .s ` D ) ( J ` Y ) ) )

  disjoint k v
  disjoint k w
  disjoint k x
  disjoint ._|_ k
  disjoint v w
  disjoint v x
  disjoint ._|_ v
  disjoint w x
  disjoint ._|_ w
  disjoint ._|_ x
  disjoint .+ k
  disjoint .+ v
  disjoint .+ w
  disjoint .+ x
  disjoint R k
  disjoint R v
  disjoint R x
  disjoint S k
  disjoint .x. k
  disjoint .x. v
  disjoint .x. w
  disjoint .x. x
  disjoint V v
  disjoint V x
  disjoint X k
  disjoint X v
  disjoint X w
  disjoint X x
  disjoint Y k
  disjoint Y v
  disjoint Y w
  disjoint Y x
  disjoint .0. x
  disjoint J f
  disjoint L f
  disjoint ._|_ f
  disjoint .+ f
  disjoint R f
  disjoint .x. f
  disjoint U f
  disjoint V f
  disjoint X f
  disjoint Y f
  disjoint f k
  disjoint f v
  disjoint f w
  disjoint f x
  assert |- ( ph -> C =/= ( 0g ` D ) )

  proof
    wph
    cC
    cD
    c0g
    cfv
    wne
    cI
    cX
    cJ
    cfv
    cfv
    #
    cQ
    wph
    @0
    cQ
    wceq
    #
    wa
    vx
    vw
    vv
    cA
    cB
    cC
    cD
    c.pl
    cQ
    cR
    cS
    c.x
    cU
    vk
    cF
    cH
    cI
    cJ
    cK
    cL
    c.mi
    cN
    c.pe
    cV
    cW
    cX
    cY
    c.0
    lcfrlem17.h
    lcfrlem17.o
    lcfrlem17.u
    lcfrlem17.v
    lcfrlem17.p
    lcfrlem17.z
    lcfrlem17.n
    lcfrlem17.a
    wph
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    @1
    lcfrlem17.k
    adantr
    wph
    cX
    cV
    c.0
    csn
    cdif
    #
    wcel
    #
    @1
    lcfrlem17.x
    adantr
    wph
    cY
    @3
    wcel
    #
    @1
    lcfrlem17.y
    adantr
    wph
    cX
    csn
    cN
    cfv
    cY
    csn
    cN
    cfv
    wne
    #
    @1
    lcfrlem17.ne
    adantr
    lcfrlem22.b
    lcfrlem24.t
    lcfrlem24.s
    lcfrlem24.q
    lcfrlem24.r
    lcfrlem24.j
    wph
    cI
    cB
    wcel
    #
    @1
    lcfrlem24.ib
    adantr
    lcfrlem24.l
    lcfrlem25.d
    wph
    cI
    cY
    cJ
    cfv
    cfv
    cQ
    wne
    #
    @1
    lcfrlem28.jn
    adantr
    lcfrlem29.i
    lcfrlem30.m
    lcfrlem30.c
    wph
    @1
    simpr
    lcfrlem33
    wph
    @0
    cQ
    wne
    #
    wa
    vx
    vw
    vv
    cA
    cB
    cC
    cD
    c.pl
    cQ
    cR
    cS
    c.x
    cU
    vk
    cF
    cH
    cI
    cJ
    cK
    cL
    c.mi
    cN
    c.pe
    cV
    cW
    cX
    cY
    c.0
    lcfrlem17.h
    lcfrlem17.o
    lcfrlem17.u
    lcfrlem17.v
    lcfrlem17.p
    lcfrlem17.z
    lcfrlem17.n
    lcfrlem17.a
    wph
    @2
    @9
    lcfrlem17.k
    adantr
    wph
    @4
    @9
    lcfrlem17.x
    adantr
    wph
    @5
    @9
    lcfrlem17.y
    adantr
    wph
    @6
    @9
    lcfrlem17.ne
    adantr
    lcfrlem22.b
    lcfrlem24.t
    lcfrlem24.s
    lcfrlem24.q
    lcfrlem24.r
    lcfrlem24.j
    wph
    @7
    @9
    lcfrlem24.ib
    adantr
    lcfrlem24.l
    lcfrlem25.d
    wph
    @8
    @9
    lcfrlem28.jn
    adantr
    lcfrlem29.i
    lcfrlem30.m
    lcfrlem30.c
    wph
    @9
    simpr
    lcfrlem32
    pm2.61dane
end
