include "cfv.mm"
include "wne.mm"
include "wceq.mm"
include "clmod.mm"
include "wcel.mm"
include "clfn.mm"
include "dvhlmod.mm"
include "cv.mm"
include "crab.mm"
include "c0g.mm"
include "eqid.mm"
include "lcfrlem10.mm"
include "lfl0.mm"
include "syl2anc.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "syl5ibrcom.mm"
include "necon3d.mm"
include "mpd.mm"

theorem lcfrlem28
  let wph: wff ph
  let vx: setvar x
  let vw: setvar w
  let vv: setvar v
  let cA: class A
  let cB: class B
  let cD: class D
  let c.pl: class .+
  let cQ: class Q
  let cR: class R
  let cS: class S
  let c.x: class .x.
  let cU: class U
  let vk: setvar k
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
  assert |- ( ph -> I =/= .0. )

  proof
    wph
    cI
    cY
    cJ
    cfv
    #
    cfv
    #
    cQ
    wne
    cI
    c.0
    wne
    lcfrlem28.jn
    wph
    cI
    c.0
    @1
    cQ
    wph
    @1
    cQ
    wceq
    cI
    c.0
    wceq
    #
    c.0
    @0
    cfv
    #
    cQ
    wceq
    #
    wph
    cU
    clmod
    wcel
    @0
    cU
    clfn
    cfv
    #
    wcel
    @4
    wph
    cU
    cH
    cK
    cW
    lcfrlem17.h
    lcfrlem17.u
    lcfrlem17.k
    dvhlmod
    wph
    vx
    vw
    vv
    vf
    cv
    cL
    cfv
    #
    c.pe
    cfv
    c.pe
    cfv
    @6
    wceq
    vf
    @5
    crab
    #
    cD
    c.pl
    cD
    c0g
    cfv
    #
    cR
    cS
    c.x
    cU
    vf
    vk
    @5
    cH
    cJ
    cK
    cL
    c.pe
    cV
    cW
    cY
    c.0
    lcfrlem17.h
    lcfrlem17.o
    lcfrlem17.u
    lcfrlem17.v
    lcfrlem17.p
    lcfrlem24.t
    lcfrlem24.s
    lcfrlem24.r
    lcfrlem17.z
    @5
    eqid
    #
    lcfrlem24.l
    lcfrlem25.d
    @8
    eqid
    @7
    eqid
    lcfrlem24.j
    lcfrlem17.k
    lcfrlem17.y
    lcfrlem10
    cS
    @5
    @0
    cU
    cQ
    c.0
    lcfrlem24.s
    lcfrlem24.q
    lcfrlem17.z
    @9
    lfl0
    syl2anc
    @2
    @1
    @3
    cQ
    cI
    c.0
    @0
    fveq2
    eqeq1d
    syl5ibrcom
    necon3d
    mpd
end
