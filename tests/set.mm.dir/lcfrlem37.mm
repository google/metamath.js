include "co.mm"
include "cv.mm"
include "cfv.mm"
include "ciun.mm"
include "wcel.mm"
include "wrex.mm"
include "cmulr.mm"
include "cvsca.mm"
include "clss.mm"
include "eqid.mm"
include "dvhlmod.mm"
include "wceq.mm"
include "clfn.mm"
include "crab.mm"
include "c0g.mm"
include "wne.mm"
include "csn.mm"
include "cdif.mm"
include "eldifsni.mm"
include "syl.mm"
include "eldifsn.mm"
include "sylanbrc.mm"
include "lcfrlem16.mm"
include "lcfrlem29.mm"
include "ldualssvscl.mm"
include "ldualssvsubcl.mm"
include "syl5eqel.mm"
include "lcfrlem36.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "eleq2d.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "eliun.mm"
include "sylibr.mm"
include "syl6eleqr.mm"

theorem lcfrlem37
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
  let c.mi: class .-
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
  assume lcfrlem28.jn: |- ( ph -> ( ( J ` Y ) ` I ) =/= Q )
  assume lcfrlem29.i: |- F = ( invr ` S )
  assume lcfrlem30.m: |- .- = ( -g ` D )
  assume lcfrlem30.c: |- C = ( ( J ` X ) .- ( ( ( F ` ( ( J ` Y ) ` I ) ) ( .r ` S ) ( ( J ` X ) ` I ) ) ( .s ` D ) ( J ` Y ) ) )
  assume lcfrlem37.g: |- ( ph -> G e. ( LSubSp ` D ) )
  assume lcfrlem37.gs: |- ( ph -> G C_ { f e. ( LFnl ` U ) | ( ._|_ ` ( ._|_ ` ( L ` f ) ) ) = ( L ` f ) } )
  assume lcfrlem37.e: |- E = U_ g e. G ( ._|_ ` ( L ` g ) )
  assume lcfrlem37.xe: |- ( ph -> X e. E )
  assume lcfrlem37.ye: |- ( ph -> Y e. E )

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
  disjoint g k
  disjoint C g
  disjoint C k
  disjoint D g
  disjoint D k
  disjoint G g
  disjoint G k
  disjoint I g
  disjoint I k
  disjoint f g
  disjoint J g
  disjoint J k
  disjoint L g
  disjoint L k
  disjoint ._|_ g
  disjoint .+ g
  disjoint Q g
  disjoint Q k
  disjoint U k
  disjoint V g
  disjoint X g
  disjoint Y g
  disjoint g ph
  disjoint k ph
  disjoint g v
  disjoint g w
  disjoint g x
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
    cC
    cG
    wcel
    @0
    cC
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
    cC
    cX
    cJ
    cfv
    #
    cI
    cY
    cJ
    cfv
    #
    cfv
    cF
    cfv
    cI
    @10
    cfv
    cS
    cmulr
    cfv
    co
    #
    @11
    cD
    cvsca
    cfv
    #
    co
    #
    c.mi
    co
    cG
    lcfrlem30.c
    wph
    cD
    cD
    clss
    cfv
    #
    cG
    c.mi
    cU
    @10
    @14
    lcfrlem25.d
    lcfrlem30.m
    @15
    eqid
    #
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
    lcfrlem37.g
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
    @18
    wceq
    vf
    cU
    clfn
    cfv
    #
    crab
    #
    cD
    @15
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
    @19
    cG
    cH
    cJ
    cK
    cL
    c.pe
    cV
    cW
    cX
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
    @19
    eqid
    #
    lcfrlem24.l
    lcfrlem25.d
    @21
    eqid
    #
    @20
    eqid
    #
    lcfrlem24.j
    lcfrlem17.k
    @16
    lcfrlem37.g
    lcfrlem37.gs
    lcfrlem37.e
    wph
    cX
    cE
    wcel
    cX
    c.0
    wne
    #
    cX
    cE
    c.0
    csn
    #
    cdif
    #
    wcel
    lcfrlem37.xe
    wph
    cX
    cV
    @26
    cdif
    #
    wcel
    @25
    lcfrlem17.x
    cX
    cV
    c.0
    eldifsni
    syl
    cX
    cE
    c.0
    eldifsn
    sylanbrc
    lcfrlem16
    wph
    cD
    cS
    @15
    @13
    cG
    cR
    cU
    @12
    @11
    lcfrlem24.s
    lcfrlem24.r
    lcfrlem25.d
    @13
    eqid
    @16
    @17
    lcfrlem37.g
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
    cF
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
    lcfrlem28.jn
    lcfrlem29.i
    lcfrlem29
    wph
    vx
    vw
    vv
    @20
    cD
    @15
    c.pl
    @21
    cR
    cS
    c.x
    cU
    vf
    vg
    vk
    cE
    @19
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
    @22
    lcfrlem24.l
    lcfrlem25.d
    @23
    @24
    lcfrlem24.j
    lcfrlem17.k
    @16
    lcfrlem37.g
    lcfrlem37.gs
    lcfrlem37.e
    wph
    cY
    cE
    wcel
    cY
    c.0
    wne
    #
    cY
    @27
    wcel
    lcfrlem37.ye
    wph
    cY
    @28
    wcel
    @29
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
    ldualssvscl
    ldualssvsubcl
    syl5eqel
    wph
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
    lcfrlem28.jn
    lcfrlem29.i
    lcfrlem30.m
    lcfrlem30.c
    lcfrlem36
    @5
    @9
    vg
    cC
    cG
    @1
    cC
    wceq
    #
    @3
    @8
    @0
    @30
    @2
    @7
    c.pe
    @1
    cC
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
    lcfrlem37.e
    syl6eleqr
end
