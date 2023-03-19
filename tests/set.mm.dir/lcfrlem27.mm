include "co.mm"
include "cv.mm"
include "cfv.mm"
include "ciun.mm"
include "wcel.mm"
include "wrex.mm"
include "wceq.mm"
include "clfn.mm"
include "crab.mm"
include "clss.mm"
include "c0g.mm"
include "eqid.mm"
include "wne.mm"
include "csn.mm"
include "cdif.mm"
include "eldifsni.mm"
include "syl.mm"
include "eldifsn.mm"
include "sylanbrc.mm"
include "lcfrlem16.mm"
include "lcfrlem26.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "eleq2d.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "eliun.mm"
include "sylibr.mm"
include "syl6eleqr.mm"

theorem lcfrlem27
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
  let vf: setvar f
  let vg: setvar g
  let vk: setvar k
  let cE: class E
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
  assume lcfrlem25.jz: |- ( ph -> ( ( J ` Y ) ` I ) = Q )
  assume lcfrlem25.in: |- ( ph -> I =/= .0. )
  assume lcfrlem27.g: |- ( ph -> G e. ( LSubSp ` D ) )
  assume lcfrlem27.gs: |- ( ph -> G C_ { f e. ( LFnl ` U ) | ( ._|_ ` ( ._|_ ` ( L ` f ) ) ) = ( L ` f ) } )
  assume lcfrlem27.e: |- E = U_ g e. G ( ._|_ ` ( L ` g ) )
  assume lcfrlem27.xe: |- ( ph -> X e. E )
  assume lcfrlem27.ye: |- ( ph -> Y e. E )

  disjoint L f
  disjoint ._|_ f
  disjoint .+ f
  disjoint R f
  disjoint .x. f
  disjoint U f
  disjoint V f
  disjoint f k
  disjoint f v
  disjoint f w
  disjoint f x
  disjoint k v
  disjoint k w
  disjoint k x
  disjoint v w
  disjoint v x
  disjoint w x
  disjoint g k
  disjoint G g
  disjoint G k
  disjoint f g
  disjoint J f
  disjoint J g
  disjoint J k
  disjoint L g
  disjoint L k
  disjoint ._|_ g
  disjoint .+ g
  disjoint U k
  disjoint V g
  disjoint X g
  disjoint Y f
  disjoint Y g
  disjoint g ph
  disjoint k ph
  disjoint g v
  disjoint g w
  disjoint g x
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
  assert |- ( ph -> ( X .+ Y ) e. E )

  proof
    wph
    cX
    cY
    c.pl
    co
    #
    vg
    cG
    vg
    cv
    #
    cL
    cfv
    #
    c.pe
    cfv
    #
    ciun
    #
    cE
    wph
    @0
    @3
    wcel
    #
    vg
    cG
    wrex
    #
    @0
    @4
    wcel
    wph
    cY
    cJ
    cfv
    #
    cG
    wcel
    @0
    @7
    cL
    cfv
    #
    c.pe
    cfv
    #
    wcel
    #
    @6
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
    @11
    wceq
    vf
    cU
    clfn
    cfv
    #
    crab
    #
    cD
    cD
    clss
    cfv
    #
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
    vg
    vk
    cE
    @12
    cG
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
    @12
    eqid
    lcfrlem24.l
    lcfrlem25.d
    @15
    eqid
    @13
    eqid
    lcfrlem24.j
    lcfrlem17.k
    @14
    eqid
    lcfrlem27.g
    lcfrlem27.gs
    lcfrlem27.e
    wph
    cY
    cE
    wcel
    cY
    c.0
    wne
    #
    cY
    cE
    c.0
    csn
    #
    cdif
    wcel
    lcfrlem27.ye
    wph
    cY
    cV
    @17
    cdif
    wcel
    @16
    lcfrlem17.y
    cY
    cV
    c.0
    eldifsni
    syl
    cY
    cE
    c.0
    eldifsn
    sylanbrc
    lcfrlem16
    wph
    vx
    vw
    vv
    cA
    cB
    cD
    c.pl
    cQ
    cR
    cS
    c.x
    cU
    vk
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
    lcfrlem17.h
    lcfrlem17.o
    lcfrlem17.u
    lcfrlem17.v
    lcfrlem17.p
    lcfrlem17.z
    lcfrlem17.n
    lcfrlem17.a
    lcfrlem17.k
    lcfrlem17.x
    lcfrlem17.y
    lcfrlem17.ne
    lcfrlem22.b
    lcfrlem24.t
    lcfrlem24.s
    lcfrlem24.q
    lcfrlem24.r
    lcfrlem24.j
    lcfrlem24.ib
    lcfrlem24.l
    lcfrlem25.d
    lcfrlem25.jz
    lcfrlem25.in
    lcfrlem26
    @5
    @10
    vg
    @7
    cG
    @1
    @7
    wceq
    #
    @3
    @9
    @0
    @18
    @2
    @8
    c.pe
    @1
    @7
    cL
    fveq2
    fveq2d
    eleq2d
    rspcev
    syl2anc
    vg
    @0
    cG
    @3
    eliun
    sylibr
    lcfrlem27.e
    syl6eleqr
end
