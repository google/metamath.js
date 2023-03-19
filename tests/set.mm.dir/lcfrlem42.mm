include "co.mm"
include "wcel.mm"
include "c0g.mm"
include "cfv.mm"
include "wceq.mm"
include "wa.mm"
include "clmod.mm"
include "cbs.mm"
include "dvhlmod.mm"
include "eqid.mm"
include "lcfrlem4.mm"
include "lmodcom.mm"
include "syl3anc.mm"
include "adantr.mm"
include "chlt.mm"
include "simpr.mm"
include "lcfrlem7.mm"
include "eqeltrd.mm"
include "wne.mm"
include "wss.mm"
include "simprl.mm"
include "simprr.mm"
include "lcfrlem41.mm"
include "pm2.61da2ne.mm"

theorem lcfrlem42
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
  let c.0: class .0.
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
  disjoint .0. f
  disjoint .0. g
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
    #
    cE
    wcel
    cX
    cU
    c0g
    cfv
    #
    cY
    @1
    wph
    cX
    @1
    wceq
    #
    wa
    #
    @0
    cY
    cX
    c.pl
    co
    #
    cE
    wph
    @0
    @4
    wceq
    #
    @2
    wph
    cU
    clmod
    wcel
    cX
    cU
    cbs
    cfv
    #
    wcel
    cY
    @6
    wcel
    @5
    wph
    cU
    cH
    cK
    cW
    lcfrlem38.h
    lcfrlem38.u
    lcfrlem38.k
    dvhlmod
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
    @6
    cW
    cX
    lcfrlem38.h
    lcfrlem38.o
    lcfrlem38.u
    @6
    eqid
    #
    lcfrlem38.l
    lcfrlem38.d
    lcfrlem38.q
    lcfrlem38.e
    lcfrlem38.k
    lcfrlem38.g
    lcfrlem38.xe
    lcfrlem4
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
    @6
    cW
    cY
    lcfrlem38.h
    lcfrlem38.o
    lcfrlem38.u
    @7
    lcfrlem38.l
    lcfrlem38.d
    lcfrlem38.q
    lcfrlem38.e
    lcfrlem38.k
    lcfrlem38.g
    lcfrlem38.ye
    lcfrlem4
    c.pl
    @6
    cU
    cX
    cY
    @7
    lcfrlem38.p
    lmodcom
    syl3anc
    adantr
    @3
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
    c.pe
    cW
    cY
    cX
    @1
    lcfrlem38.h
    lcfrlem38.o
    lcfrlem38.u
    lcfrlem38.p
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
    @2
    lcfrlem38.k
    adantr
    wph
    cG
    cQ
    wcel
    #
    @2
    lcfrlem38.g
    adantr
    lcfrlem38.e
    wph
    cY
    cE
    wcel
    #
    @2
    lcfrlem38.ye
    adantr
    @1
    eqid
    #
    wph
    @2
    simpr
    lcfrlem7
    eqeltrd
    wph
    cY
    @1
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
    c.pe
    cW
    cX
    cY
    @1
    lcfrlem38.h
    lcfrlem38.o
    lcfrlem38.u
    lcfrlem38.p
    lcfrlem38.l
    lcfrlem38.d
    lcfrlem38.q
    wph
    @8
    @12
    lcfrlem38.k
    adantr
    wph
    @9
    @12
    lcfrlem38.g
    adantr
    lcfrlem38.e
    wph
    cX
    cE
    wcel
    #
    @12
    lcfrlem38.xe
    adantr
    @11
    wph
    @12
    simpr
    lcfrlem7
    wph
    cX
    @1
    wne
    #
    cY
    @1
    wne
    #
    wa
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
    c.pe
    cW
    cX
    cY
    @1
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
    @8
    @16
    lcfrlem38.k
    adantr
    wph
    @9
    @16
    lcfrlem38.g
    adantr
    wph
    cG
    cC
    wss
    @16
    lcfrlem38.gs
    adantr
    wph
    @13
    @16
    lcfrlem38.xe
    adantr
    wph
    @10
    @16
    lcfrlem38.ye
    adantr
    @11
    wph
    @14
    @15
    simprl
    wph
    @14
    @15
    simprr
    lcfrlem41
    pm2.61da2ne
end
