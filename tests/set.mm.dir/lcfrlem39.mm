include "csca.mm"
include "cfv.mm"
include "cbs.mm"
include "cvsca.mm"
include "csn.mm"
include "cdif.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wrex.mm"
include "crio.mm"
include "cmpt.mm"
include "eqid.mm"
include "weq.mm"
include "oveq1.mm"
include "oveq2d.mm"
include "eqeq2d.mm"
include "rexbidv.mm"
include "cbvriotav.mm"
include "mpteq2i.mm"
include "lcfrlem38.mm"

theorem lcfrlem39
  let wph: wff ph
  let cB: class B
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
  let cI: class I
  let cK: class K
  let cL: class L
  let cN: class N
  let c.pe: class ._|_
  let cW: class W
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  let vk: setvar k
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
  assume lcfrlem38.sp: |- N = ( LSpan ` U )
  assume lcfrlem38.ne: |- ( ph -> ( N ` { X } ) =/= ( N ` { Y } ) )
  assume lcfrlem38.b: |- B = ( ( N ` { X , Y } ) i^i ( ._|_ ` { ( X .+ Y ) } ) )
  assume lcfrlem38.i: |- ( ph -> I e. B )
  assume lcfrlem38.n: |- ( ph -> I =/= .0. )

  disjoint D g
  disjoint G g
  disjoint I g
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
    vx
    vw
    vv
    cB
    cC
    cD
    c.pl
    cQ
    cU
    csca
    cfv
    #
    cbs
    cfv
    #
    @0
    cU
    cvsca
    cfv
    #
    cU
    vf
    vg
    vk
    cE
    cF
    cG
    cH
    cI
    vx
    cU
    cbs
    cfv
    #
    c.0
    csn
    cdif
    #
    vv
    @3
    vv
    cv
    #
    vw
    cv
    #
    vj
    cv
    #
    vx
    cv
    #
    @2
    co
    #
    c.pl
    co
    #
    wceq
    #
    vw
    @8
    csn
    c.pe
    cfv
    #
    wrex
    #
    vj
    @1
    crio
    #
    cmpt
    #
    cmpt
    cK
    cL
    cN
    c.pe
    @3
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
    lcfrlem38.k
    lcfrlem38.g
    lcfrlem38.gs
    lcfrlem38.xe
    lcfrlem38.ye
    lcfrlem38.z
    lcfrlem38.x
    lcfrlem38.y
    lcfrlem38.sp
    lcfrlem38.ne
    lcfrlem38.b
    lcfrlem38.i
    lcfrlem38.n
    @3
    eqid
    @2
    eqid
    @0
    eqid
    @1
    eqid
    vx
    @4
    @15
    vv
    @3
    @5
    @6
    vk
    cv
    #
    @8
    @2
    co
    #
    c.pl
    co
    #
    wceq
    #
    vw
    @12
    wrex
    #
    vk
    @1
    crio
    #
    cmpt
    vv
    @3
    @14
    @21
    @13
    @20
    vj
    vk
    @1
    vj
    vk
    weq
    #
    @11
    @19
    vw
    @12
    @22
    @10
    @18
    @5
    @22
    @9
    @17
    @6
    c.pl
    @7
    @16
    @8
    @2
    oveq1
    oveq2d
    eqeq2d
    rexbidv
    cbvriotav
    mpteq2i
    mpteq2i
    lcfrlem38
end
