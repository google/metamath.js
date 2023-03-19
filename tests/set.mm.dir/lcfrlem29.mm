include "crg.mm"
include "wcel.mm"
include "cfv.mm"
include "cmulr.mm"
include "co.mm"
include "clmod.mm"
include "dvhlmod.mm"
include "lmodring.mm"
include "syl.mm"
include "cdr.mm"
include "wne.mm"
include "clvec.mm"
include "dvhlvec.mm"
include "lvecdrng.mm"
include "clfn.mm"
include "cv.mm"
include "wceq.mm"
include "crab.mm"
include "c0g.mm"
include "eqid.mm"
include "lcfrlem10.mm"
include "clss.mm"
include "lcfrlem22.mm"
include "lsatlssel.mm"
include "lssel.mm"
include "syl2anc.mm"
include "lflcl.mm"
include "syl3anc.mm"
include "drnginvrcl.mm"
include "ringcl.mm"

theorem lcfrlem29
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
  let cF: class F
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
  assume lcfrlem29.i: |- F = ( invr ` S )

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
  assert |- ( ph -> ( ( F ` ( ( J ` Y ) ` I ) ) ( .r ` S ) ( ( J ` X ) ` I ) ) e. R )

  proof
    wph
    cS
    crg
    wcel
    #
    cI
    cY
    cJ
    cfv
    #
    cfv
    #
    cF
    cfv
    #
    cR
    wcel
    #
    cI
    cX
    cJ
    cfv
    #
    cfv
    #
    cR
    wcel
    #
    @3
    @6
    cS
    cmulr
    cfv
    #
    co
    cR
    wcel
    wph
    cU
    clmod
    wcel
    #
    @0
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
    cS
    cU
    lcfrlem24.s
    lmodring
    syl
    wph
    cS
    cdr
    wcel
    #
    @2
    cR
    wcel
    #
    @2
    cQ
    wne
    @4
    wph
    cU
    clvec
    wcel
    @11
    wph
    cU
    cH
    cK
    cW
    lcfrlem17.h
    lcfrlem17.u
    lcfrlem17.k
    dvhlvec
    cS
    cU
    lcfrlem24.s
    lvecdrng
    syl
    wph
    @9
    @1
    cU
    clfn
    cfv
    #
    wcel
    cI
    cV
    wcel
    #
    @12
    @10
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
    @15
    wceq
    vf
    @13
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
    @13
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
    eqid
    #
    lcfrlem24.l
    lcfrlem25.d
    @17
    eqid
    #
    @16
    eqid
    #
    lcfrlem24.j
    lcfrlem17.k
    lcfrlem17.y
    lcfrlem10
    wph
    cB
    cU
    clss
    cfv
    #
    wcel
    cI
    cB
    wcel
    @14
    wph
    cA
    @21
    cB
    cU
    @21
    eqid
    #
    lcfrlem17.a
    @10
    wph
    cA
    cB
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
    lcfrlem22.b
    lcfrlem22
    lsatlssel
    lcfrlem24.ib
    @21
    cB
    cV
    cU
    cI
    lcfrlem17.v
    @22
    lssel
    syl2anc
    #
    cS
    @13
    @1
    cR
    cV
    cU
    cI
    clmod
    lcfrlem24.s
    lcfrlem24.r
    lcfrlem17.v
    @18
    lflcl
    syl3anc
    lcfrlem28.jn
    cR
    cS
    cF
    @2
    cQ
    lcfrlem24.r
    lcfrlem24.q
    lcfrlem29.i
    drnginvrcl
    syl3anc
    wph
    @9
    @5
    @13
    wcel
    @14
    @7
    @10
    wph
    vx
    vw
    vv
    @16
    cD
    c.pl
    @17
    cR
    cS
    c.x
    cU
    vf
    vk
    @13
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
    @18
    lcfrlem24.l
    lcfrlem25.d
    @19
    @20
    lcfrlem24.j
    lcfrlem17.k
    lcfrlem17.x
    lcfrlem10
    @23
    cS
    @13
    @5
    cR
    cV
    cU
    cI
    clmod
    lcfrlem24.s
    lcfrlem24.r
    lcfrlem17.v
    @18
    lflcl
    syl3anc
    cR
    cS
    @8
    @3
    @6
    lcfrlem24.r
    @8
    eqid
    ringcl
    syl3anc
end
