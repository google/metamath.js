include "cfv.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "csn.mm"
include "wrex.mm"
include "crio.mm"
include "cmpt.mm"
include "lcfrlem8.mm"
include "fveq2d.mm"
include "eqid.mm"
include "dochsnkr2.mm"
include "eqtrd.mm"

theorem lcfrlem11
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
  assume lcfrlem10.x: |- ( ph -> X e. ( V \ { .0. } ) )

  disjoint k v
  disjoint k w
  disjoint .+ k
  disjoint v w
  disjoint .+ v
  disjoint .+ w
  disjoint ._|_ k
  disjoint ._|_ v
  disjoint R k
  disjoint R v
  disjoint S k
  disjoint .x. k
  disjoint .x. v
  disjoint .x. w
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
  assert |- ( ph -> ( L ` ( J ` X ) ) = ( ._|_ ` { X } ) )

  proof
    wph
    cX
    cJ
    cfv
    #
    cL
    cfv
    vv
    cV
    vv
    cv
    vw
    cv
    vk
    cv
    cX
    c.x
    co
    c.pl
    co
    wceq
    vw
    cX
    csn
    c.pe
    cfv
    #
    wrex
    vk
    cR
    crio
    cmpt
    #
    cL
    cfv
    @1
    wph
    @0
    @2
    cL
    wph
    vx
    vw
    vv
    cC
    cD
    c.pl
    cQ
    cR
    cS
    c.x
    cU
    vf
    vk
    cF
    cH
    cJ
    cK
    cL
    c.pe
    cV
    cW
    cX
    c.0
    lcf1o.h
    lcf1o.o
    lcf1o.u
    lcf1o.v
    lcf1o.a
    lcf1o.t
    lcf1o.s
    lcf1o.r
    lcf1o.z
    lcf1o.f
    lcf1o.l
    lcf1o.d
    lcf1o.q
    lcf1o.c
    lcf1o.j
    lcflo.k
    lcfrlem10.x
    lcfrlem8
    fveq2d
    wph
    vw
    vv
    cS
    c.pl
    cR
    c.x
    cU
    vk
    @2
    cH
    cK
    cL
    c.pe
    cV
    cW
    cX
    c.0
    lcf1o.h
    lcf1o.o
    lcf1o.u
    lcf1o.v
    lcf1o.z
    lcf1o.a
    lcf1o.t
    lcf1o.l
    lcf1o.s
    lcf1o.r
    @2
    eqid
    lcflo.k
    lcfrlem10.x
    dochsnkr2
    eqtrd
end
