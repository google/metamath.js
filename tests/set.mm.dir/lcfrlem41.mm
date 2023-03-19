include "co.mm"
include "wcel.mm"
include "csn.mm"
include "clspn.mm"
include "cfv.mm"
include "wceq.mm"
include "wa.mm"
include "eqid.mm"
include "chlt.mm"
include "adantr.mm"
include "simpr.mm"
include "lcfrlem6.mm"
include "wne.mm"
include "wss.mm"
include "lcfrlem40.mm"
include "pm2.61dane.mm"

theorem lcfrlem41
  let wph: wff ph
  let cC: class C
  let cD: class D
  let c.pl: class .+
  let cQ: class Q
  let cU: class U
  let vf: setvar f
  let vg: setvar g
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H
  let cK: class K
  let cL: class L
  let c.pe: class ._|_
  let cW: class W
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  let vk: setvar k
  let cI: class I
  let cJ: class J
  let vj: setvar j
  let vv: setvar v
  let vw: setvar w
  let vx: setvar x
  let cR: class R
  let cS: class S
  let c.x: class .x.
  let cV: class V
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

  disjoint D g
  disjoint G g
  disjoint f g
  disjoint L f
  disjoint L g
  disjoint ._|_ f
  disjoint ._|_ g
  disjoint .+ f
  disjoint .+ g
  disjoint U f
  disjoint U g
  disjoint X f
  disjoint X g
  disjoint Y f
  disjoint Y g
  disjoint .0. f
  disjoint .0. g
  disjoint g ph
  disjoint g k
  disjoint D k
  disjoint G k
  disjoint I g
  disjoint I k
  disjoint f k
  disjoint J f
  disjoint J g
  disjoint J k
  disjoint L k
  disjoint f j
  disjoint f v
  disjoint f w
  disjoint f x
  disjoint g j
  disjoint g v
  disjoint g w
  disjoint g x
  disjoint j k
  disjoint j v
  disjoint j w
  disjoint j x
  disjoint ._|_ j
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
  disjoint .+ j
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
  disjoint U j
  disjoint U k
  disjoint U v
  disjoint U w
  disjoint U x
  disjoint V f
  disjoint V g
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
  disjoint .0. k
  disjoint .0. x
  disjoint k ph
  assert |- ( ph -> ( X .+ Y ) e. E )

  proof
    wph
    cX
    cY
    c.pl
    co
    cE
    wcel
    cX
    csn
    cU
    clspn
    cfv
    #
    cfv
    #
    cY
    csn
    @0
    cfv
    #
    wph
    @1
    @2
    wceq
    #
    wa
    cD
    c.pl
    cQ
    cU
    vg
    cE
    cG
    cH
    cK
    cL
    @0
    c.pe
    cW
    cX
    cY
    lcfrlem38.h
    lcfrlem38.o
    lcfrlem38.u
    lcfrlem38.p
    @0
    eqid
    #
    lcfrlem38.l
    lcfrlem38.d
    lcfrlem38.q
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
    cG
    cQ
    wcel
    #
    @3
    lcfrlem38.g
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
    wph
    @3
    simpr
    lcfrlem6
    wph
    @1
    @2
    wne
    #
    wa
    cC
    cD
    c.pl
    cQ
    cU
    vf
    vg
    cE
    cF
    cG
    cH
    cK
    cL
    @0
    c.pe
    cW
    cX
    cY
    c.0
    lcfrlem38.h
    lcfrlem38.o
    lcfrlem38.u
    lcfrlem38.p
    lcfrlem38.f
    lcfrlem38.l
    lcfrlem38.d
    lcfrlem38.q
    lcfrlem38.c
    lcfrlem38.e
    wph
    @5
    @9
    lcfrlem38.k
    adantr
    wph
    @6
    @9
    lcfrlem38.g
    adantr
    wph
    cG
    cC
    wss
    @9
    lcfrlem38.gs
    adantr
    wph
    @7
    @9
    lcfrlem38.xe
    adantr
    wph
    @8
    @9
    lcfrlem38.ye
    adantr
    lcfrlem38.z
    wph
    cX
    c.0
    wne
    @9
    lcfrlem38.x
    adantr
    wph
    cY
    c.0
    wne
    @9
    lcfrlem38.y
    adantr
    @4
    wph
    @9
    simpr
    lcfrlem40
    pm2.61dane
end
