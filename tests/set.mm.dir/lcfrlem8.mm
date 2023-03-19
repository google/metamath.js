include "csn.mm"
include "cdif.mm"
include "wcel.mm"
include "cfv.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wrex.mm"
include "crio.mm"
include "cmpt.mm"
include "sneq.mm"
include "fveq2d.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "eqeq2d.mm"
include "rexeqbidv.mm"
include "riotabidv.mm"
include "mpteq2dv.mm"
include "cbs.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "mptex.mm"
include "fvmpt.mm"
include "syl.mm"

theorem lcfrlem8
  let wph: wff ph
  let vx: setvar x
  let vw: setvar w
  let vv: setvar v
  let cC: class C
  let cD: class D
  let c.pl: class .+
  let cQ: class Q
  let cR: class R
  let cS: class S
  let c.x: class .x.
  let cU: class U
  let vf: setvar f
  let vk: setvar k
  let cF: class F
  let cH: class H
  let cJ: class J
  let cK: class K
  let cL: class L
  let c.pe: class ._|_
  let cV: class V
  let cW: class W
  let cX: class X
  let c.0: class .0.
  assume lcf1o.h: |- H = ( LHyp ` K )
  assume lcf1o.o: |- ._|_ = ( ( ocH ` K ) ` W )
  assume lcf1o.u: |- U = ( ( DVecH ` K ) ` W )
  assume lcf1o.v: |- V = ( Base ` U )
  assume lcf1o.a: |- .+ = ( +g ` U )
  assume lcf1o.t: |- .x. = ( .s ` U )
  assume lcf1o.s: |- S = ( Scalar ` U )
  assume lcf1o.r: |- R = ( Base ` S )
  assume lcf1o.z: |- .0. = ( 0g ` U )
  assume lcf1o.f: |- F = ( LFnl ` U )
  assume lcf1o.l: |- L = ( LKer ` U )
  assume lcf1o.d: |- D = ( LDual ` U )
  assume lcf1o.q: |- Q = ( 0g ` D )
  assume lcf1o.c: |- C = { f e. F | ( ._|_ ` ( ._|_ ` ( L ` f ) ) ) = ( L ` f ) }
  assume lcf1o.j: |- J = ( x e. ( V \ { .0. } ) |-> ( v e. V |-> ( iota_ k e. R E. w e. ( ._|_ ` { x } ) v = ( w .+ ( k .x. x ) ) ) ) )
  assume lcflo.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume lcfrlem8.x: |- ( ph -> X e. ( V \ { .0. } ) )

  disjoint w x
  disjoint ._|_ w
  disjoint ._|_ x
  disjoint .0. x
  disjoint v x
  disjoint V v
  disjoint V x
  disjoint .x. x
  disjoint k v
  disjoint k w
  disjoint k x
  disjoint X k
  disjoint v w
  disjoint X v
  disjoint X w
  disjoint X x
  disjoint .+ x
  disjoint R x
  assert |- ( ph -> ( J ` X ) = ( v e. V |-> ( iota_ k e. R E. w e. ( ._|_ ` { X } ) v = ( w .+ ( k .x. X ) ) ) ) )

  proof
    wph
    cX
    cV
    c.0
    csn
    cdif
    #
    wcel
    cX
    cJ
    cfv
    vv
    cV
    vv
    cv
    #
    vw
    cv
    #
    vk
    cv
    #
    cX
    c.x
    co
    #
    c.pl
    co
    #
    wceq
    #
    vw
    cX
    csn
    #
    c.pe
    cfv
    #
    wrex
    #
    vk
    cR
    crio
    #
    cmpt
    #
    wceq
    lcfrlem8.x
    vx
    cX
    vv
    cV
    @1
    @2
    @3
    vx
    cv
    #
    c.x
    co
    #
    c.pl
    co
    #
    wceq
    #
    vw
    @12
    csn
    #
    c.pe
    cfv
    #
    wrex
    #
    vk
    cR
    crio
    #
    cmpt
    @11
    @0
    cJ
    @12
    cX
    wceq
    #
    vv
    cV
    @19
    @10
    @20
    @18
    @9
    vk
    cR
    @20
    @15
    @6
    vw
    @17
    @8
    @20
    @16
    @7
    c.pe
    @12
    cX
    sneq
    fveq2d
    @20
    @14
    @5
    @1
    @20
    @13
    @4
    @2
    c.pl
    @12
    cX
    @3
    c.x
    oveq2
    oveq2d
    eqeq2d
    rexeqbidv
    riotabidv
    mpteq2dv
    lcf1o.j
    vv
    cV
    @10
    cV
    cU
    cbs
    cfv
    cvv
    lcf1o.v
    cU
    cbs
    fvex
    eqeltri
    mptex
    fvmpt
    syl
end
