include "co.mm"
include "cfv.mm"
include "wcel.mm"
include "csn.mm"
include "wss.mm"
include "wceq.mm"
include "lcfrlem17.mm"
include "eldifad.mm"
include "dochocsn.mm"
include "lcfrlem25.mm"
include "fveq2d.mm"
include "eqtr3d.mm"
include "eqimss.mm"
include "syl.mm"
include "clss.mm"
include "eqid.mm"
include "dvhlmod.mm"
include "chlt.mm"
include "wa.mm"
include "clfn.mm"
include "cv.mm"
include "crab.mm"
include "c0g.mm"
include "lcfrlem10.mm"
include "lkrssv.mm"
include "dochlss.mm"
include "syl2anc.mm"
include "lspsnel5.mm"
include "mpbird.mm"

theorem lcfrlem26
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
  assume lcfrlem25.jz: |- ( ph -> ( ( J ` Y ) ` I ) = Q )
  assume lcfrlem25.in: |- ( ph -> I =/= .0. )

  disjoint k v
  disjoint k w
  disjoint k x
  disjoint v w
  disjoint v x
  disjoint w x
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
  assert |- ( ph -> ( X .+ Y ) e. ( ._|_ ` ( L ` ( J ` Y ) ) ) )

  proof
    wph
    cX
    cY
    c.pl
    co
    #
    cY
    cJ
    cfv
    #
    cL
    cfv
    #
    c.pe
    cfv
    #
    wcel
    @0
    csn
    #
    cN
    cfv
    #
    @3
    wss
    #
    wph
    @5
    @3
    wceq
    @6
    wph
    @4
    c.pe
    cfv
    #
    c.pe
    cfv
    @5
    @3
    wph
    cU
    cH
    cK
    cN
    c.pe
    cV
    cW
    @0
    lcfrlem17.h
    lcfrlem17.u
    lcfrlem17.o
    lcfrlem17.v
    lcfrlem17.n
    lcfrlem17.k
    wph
    @0
    cV
    c.0
    csn
    wph
    cA
    c.pl
    cU
    cH
    cK
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
    lcfrlem17
    eldifad
    #
    dochocsn
    wph
    @7
    @2
    c.pe
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
    lcfrlem25
    fveq2d
    eqtr3d
    @5
    @3
    eqimss
    syl
    wph
    cU
    clss
    cfv
    #
    @3
    cN
    cV
    cU
    @0
    lcfrlem17.v
    @9
    eqid
    #
    lcfrlem17.n
    wph
    cU
    cH
    cK
    cW
    lcfrlem17.h
    lcfrlem17.u
    lcfrlem17.k
    dvhlmod
    #
    wph
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    @2
    cV
    wss
    @3
    @9
    wcel
    lcfrlem17.k
    wph
    cU
    clfn
    cfv
    #
    @1
    cL
    cV
    cU
    lcfrlem17.v
    @12
    eqid
    #
    lcfrlem24.l
    @11
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
    @14
    wceq
    vf
    @12
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
    @12
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
    @13
    lcfrlem24.l
    lcfrlem25.d
    @16
    eqid
    @15
    eqid
    lcfrlem24.j
    lcfrlem17.k
    lcfrlem17.y
    lcfrlem10
    lkrssv
    @9
    cU
    cH
    cK
    c.pe
    cV
    cW
    @2
    lcfrlem17.h
    lcfrlem17.u
    lcfrlem17.v
    @10
    lcfrlem17.o
    dochlss
    syl2anc
    @8
    lspsnel5
    mpbird
end
