include "cfv.mm"
include "csn.mm"
include "lcfrlem11.mm"
include "eldifad.mm"
include "snssd.mm"
include "dochocsp.mm"
include "eqtr4d.mm"
include "fveq2d.mm"
include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cdih.mm"
include "crn.mm"
include "wceq.mm"
include "eqid.mm"
include "dihlsprn.mm"
include "syl2anc.mm"
include "dochoc.mm"
include "eqtrd.mm"

theorem lcfrlem14
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
  let cN: class N
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
  assume lcfrlem14.n: |- N = ( LSpan ` U )

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
  disjoint f k
  disjoint f v
  disjoint f w
  disjoint .+ f
  disjoint F f
  disjoint L f
  disjoint ._|_ f
  disjoint R f
  disjoint .x. f
  disjoint V f
  disjoint f x
  disjoint k x
  disjoint J f
  disjoint X f
  disjoint X k
  disjoint v x
  disjoint X v
  disjoint w x
  disjoint X w
  disjoint X x
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
  assert |- ( ph -> ( ._|_ ` ( L ` ( J ` X ) ) ) = ( N ` { X } ) )

  proof
    wph
    cX
    cJ
    cfv
    cL
    cfv
    #
    c.pe
    cfv
    cX
    csn
    #
    cN
    cfv
    #
    c.pe
    cfv
    #
    c.pe
    cfv
    #
    @2
    wph
    @0
    @3
    c.pe
    wph
    @0
    @1
    c.pe
    cfv
    @3
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
    lcfrlem11
    wph
    cU
    cH
    cK
    cN
    c.pe
    cV
    cW
    @1
    lcf1o.h
    lcf1o.u
    lcf1o.o
    lcf1o.v
    lcfrlem14.n
    lcflo.k
    wph
    cX
    cV
    wph
    cX
    cV
    c.0
    csn
    lcfrlem10.x
    eldifad
    #
    snssd
    dochocsp
    eqtr4d
    fveq2d
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
    cW
    cK
    cdih
    cfv
    cfv
    #
    crn
    wcel
    #
    @4
    @2
    wceq
    lcflo.k
    wph
    @6
    cX
    cV
    wcel
    @8
    lcflo.k
    @5
    cU
    cH
    @7
    cK
    cN
    cV
    cW
    cX
    lcf1o.h
    lcf1o.u
    lcf1o.v
    lcfrlem14.n
    @7
    eqid
    #
    dihlsprn
    syl2anc
    cH
    @7
    cK
    c.pe
    cW
    @2
    lcf1o.h
    @9
    lcf1o.o
    dochoc
    syl2anc
    eqtrd
end
