include "co.mm"
include "wcel.mm"
include "cfv.mm"
include "c0g.mm"
include "wceq.mm"
include "wa.mm"
include "clsa.mm"
include "eqid.mm"
include "chlt.mm"
include "adantr.mm"
include "csn.mm"
include "cdif.mm"
include "wne.mm"
include "lcfrlem4.mm"
include "eldifsn.mm"
include "sylanbrc.mm"
include "simpr.mm"
include "clss.mm"
include "syl6eleq.mm"
include "cv.mm"
include "clfn.mm"
include "crab.mm"
include "wss.mm"
include "syl6sseq.mm"
include "lcfrlem27.mm"
include "cinvr.mm"
include "cmulr.mm"
include "cvsca.mm"
include "csg.mm"
include "lcfrlem37.mm"
include "pm2.61dane.mm"

theorem lcfrlem38
  let wph: wff ph
  let vx: setvar x
  let vw: setvar w
  let vv: setvar v
  let cB: class B
  let cC: class C
  let cD: class D
  let c.pl: class .+
  let cQ: class Q
  let cR: class R
  let cS: class S
  let c.x: class .x.
  let cU: class U
  let vf: setvar f
  let vg: setvar g
  let vk: setvar k
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H
  let cI: class I
  let cJ: class J
  let cK: class K
  let cL: class L
  let cN: class N
  let c.pe: class ._|_
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  let vj: setvar j
  assume lcfrlem38.h: |- H = ( LHyp ` K )
  assume lcfrlem38.o: |- ._|_ = ( ( ocH ` K ) ` W )
  assume lcfrlem38.u: |- U = ( ( DVecH ` K ) ` W )
  assume lcfrlem38.p: |- .+ = ( +g ` U )
  assume lcfrlem38.f: |- F = ( LFnl ` U )
  assume lcfrlem38.l: |- L = ( LKer ` U )
  assume lcfrlem38.d: |- D = ( LDual ` U )
  assume lcfrlem38.q: |- Q = ( LSubSp ` D )
  assume lcfrlem38.c: |- C = { f e. ( LFnl ` U ) | ( ._|_ ` ( ._|_ ` ( L ` f ) ) ) = ( L ` f ) }
  assume lcfrlem38.e: |- E = U_ g e. G ( ._|_ ` ( L ` g ) )
  assume lcfrlem38.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume lcfrlem38.g: |- ( ph -> G e. Q )
  assume lcfrlem38.gs: |- ( ph -> G C_ C )
  assume lcfrlem38.xe: |- ( ph -> X e. E )
  assume lcfrlem38.ye: |- ( ph -> Y e. E )
  assume lcfrlem38.z: |- .0. = ( 0g ` U )
  assume lcfrlem38.x: |- ( ph -> X =/= .0. )
  assume lcfrlem38.y: |- ( ph -> Y =/= .0. )
  assume lcfrlem38.sp: |- N = ( LSpan ` U )
  assume lcfrlem38.ne: |- ( ph -> ( N ` { X } ) =/= ( N ` { Y } ) )
  assume lcfrlem38.b: |- B = ( ( N ` { X , Y } ) i^i ( ._|_ ` { ( X .+ Y ) } ) )
  assume lcfrlem38.i: |- ( ph -> I e. B )
  assume lcfrlem38.n: |- ( ph -> I =/= .0. )
  assume lcfrlem38.v: |- V = ( Base ` U )
  assume lcfrlem38.t: |- .x. = ( .s ` U )
  assume lcfrlem38.s: |- S = ( Scalar ` U )
  assume lcfrlem38.r: |- R = ( Base ` S )
  assume lcfrlem38.j: |- J = ( x e. ( V \ { .0. } ) |-> ( v e. V |-> ( iota_ k e. R E. w e. ( ._|_ ` { x } ) v = ( w .+ ( k .x. x ) ) ) ) )

  disjoint g k
  disjoint D g
  disjoint D k
  disjoint G g
  disjoint G k
  disjoint I g
  disjoint I k
  disjoint f g
  disjoint f k
  disjoint J f
  disjoint J g
  disjoint J k
  disjoint L f
  disjoint L g
  disjoint L k
  disjoint f v
  disjoint f w
  disjoint f x
  disjoint ._|_ f
  disjoint g v
  disjoint g w
  disjoint g x
  disjoint ._|_ g
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
  disjoint .+ f
  disjoint .+ g
  disjoint .+ k
  disjoint .+ v
  disjoint .+ w
  disjoint .+ x
  disjoint R f
  disjoint R k
  disjoint R v
  disjoint R x
  disjoint S g
  disjoint S k
  disjoint .x. f
  disjoint .x. k
  disjoint .x. v
  disjoint .x. w
  disjoint .x. x
  disjoint U f
  disjoint U g
  disjoint U k
  disjoint U v
  disjoint U w
  disjoint U x
  disjoint V f
  disjoint V g
  disjoint V v
  disjoint V x
  disjoint X f
  disjoint X g
  disjoint X k
  disjoint X v
  disjoint X w
  disjoint X x
  disjoint Y f
  disjoint Y g
  disjoint Y k
  disjoint Y v
  disjoint Y w
  disjoint Y x
  disjoint .0. f
  disjoint .0. g
  disjoint .0. k
  disjoint .0. x
  disjoint g ph
  disjoint k ph
  disjoint f j
  disjoint g j
  disjoint j k
  disjoint j v
  disjoint j w
  disjoint j x
  disjoint ._|_ j
  disjoint .+ j
  disjoint U j
  assert |- ( ph -> ( X .+ Y ) e. E )

  proof
    wph
    cX
    cY
    c.pl
    co
    cE
    wcel
    cI
    cY
    cJ
    cfv
    #
    cfv
    #
    cS
    c0g
    cfv
    #
    wph
    @1
    @2
    wceq
    #
    wa
    vx
    vw
    vv
    cU
    clsa
    cfv
    #
    cB
    cD
    c.pl
    @2
    cR
    cS
    c.x
    cU
    vf
    vg
    vk
    cE
    cG
    cH
    cI
    cJ
    cK
    cL
    cN
    c.pe
    cV
    cW
    cX
    cY
    c.0
    lcfrlem38.h
    lcfrlem38.o
    lcfrlem38.u
    lcfrlem38.v
    lcfrlem38.p
    lcfrlem38.z
    lcfrlem38.sp
    @4
    eqid
    #
    wph
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    @3
    lcfrlem38.k
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
    @3
    wph
    cX
    cV
    wcel
    cX
    c.0
    wne
    @8
    wph
    cD
    cQ
    cU
    vg
    cE
    cG
    cH
    cK
    cL
    c.pe
    cV
    cW
    cX
    lcfrlem38.h
    lcfrlem38.o
    lcfrlem38.u
    lcfrlem38.v
    lcfrlem38.l
    lcfrlem38.d
    lcfrlem38.q
    lcfrlem38.e
    lcfrlem38.k
    lcfrlem38.g
    lcfrlem38.xe
    lcfrlem4
    lcfrlem38.x
    cX
    cV
    c.0
    eldifsn
    sylanbrc
    #
    adantr
    wph
    cY
    @7
    wcel
    #
    @3
    wph
    cY
    cV
    wcel
    cY
    c.0
    wne
    @10
    wph
    cD
    cQ
    cU
    vg
    cE
    cG
    cH
    cK
    cL
    c.pe
    cV
    cW
    cY
    lcfrlem38.h
    lcfrlem38.o
    lcfrlem38.u
    lcfrlem38.v
    lcfrlem38.l
    lcfrlem38.d
    lcfrlem38.q
    lcfrlem38.e
    lcfrlem38.k
    lcfrlem38.g
    lcfrlem38.ye
    lcfrlem4
    lcfrlem38.y
    cY
    cV
    c.0
    eldifsn
    sylanbrc
    #
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
    @3
    lcfrlem38.ne
    adantr
    lcfrlem38.b
    lcfrlem38.t
    lcfrlem38.s
    @2
    eqid
    #
    lcfrlem38.r
    lcfrlem38.j
    wph
    cI
    cB
    wcel
    #
    @3
    lcfrlem38.i
    adantr
    lcfrlem38.l
    lcfrlem38.d
    wph
    @3
    simpr
    wph
    cI
    c.0
    wne
    @3
    lcfrlem38.n
    adantr
    wph
    cG
    cD
    clss
    cfv
    #
    wcel
    #
    @3
    wph
    cG
    cQ
    @15
    lcfrlem38.g
    lcfrlem38.q
    syl6eleq
    #
    adantr
    wph
    cG
    vf
    cv
    cL
    cfv
    #
    c.pe
    cfv
    c.pe
    cfv
    @18
    wceq
    vf
    cU
    clfn
    cfv
    crab
    #
    wss
    #
    @3
    wph
    cG
    cC
    @19
    lcfrlem38.gs
    lcfrlem38.c
    syl6sseq
    #
    adantr
    lcfrlem38.e
    wph
    cX
    cE
    wcel
    #
    @3
    lcfrlem38.xe
    adantr
    wph
    cY
    cE
    wcel
    #
    @3
    lcfrlem38.ye
    adantr
    lcfrlem27
    wph
    @1
    @2
    wne
    #
    wa
    vx
    vw
    vv
    @4
    cB
    cX
    cJ
    cfv
    #
    @1
    cS
    cinvr
    cfv
    #
    cfv
    cI
    @25
    cfv
    cS
    cmulr
    cfv
    co
    @0
    cD
    cvsca
    cfv
    co
    cD
    csg
    cfv
    #
    co
    #
    cD
    c.pl
    @2
    cR
    cS
    c.x
    cU
    vf
    vg
    vk
    cE
    @26
    cG
    cH
    cI
    cJ
    cK
    cL
    @27
    cN
    c.pe
    cV
    cW
    cX
    cY
    c.0
    lcfrlem38.h
    lcfrlem38.o
    lcfrlem38.u
    lcfrlem38.v
    lcfrlem38.p
    lcfrlem38.z
    lcfrlem38.sp
    @5
    wph
    @6
    @24
    lcfrlem38.k
    adantr
    wph
    @8
    @24
    @9
    adantr
    wph
    @10
    @24
    @11
    adantr
    wph
    @12
    @24
    lcfrlem38.ne
    adantr
    lcfrlem38.b
    lcfrlem38.t
    lcfrlem38.s
    @13
    lcfrlem38.r
    lcfrlem38.j
    wph
    @14
    @24
    lcfrlem38.i
    adantr
    lcfrlem38.l
    lcfrlem38.d
    wph
    @24
    simpr
    @26
    eqid
    @27
    eqid
    @28
    eqid
    wph
    @16
    @24
    @17
    adantr
    wph
    @20
    @24
    @21
    adantr
    lcfrlem38.e
    wph
    @22
    @24
    lcfrlem38.xe
    adantr
    wph
    @23
    @24
    lcfrlem38.ye
    adantr
    lcfrlem37
    pm2.61dane
end
