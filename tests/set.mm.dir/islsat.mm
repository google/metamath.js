include "wcel.mm"
include "csn.mm"
include "cdif.mm"
include "cv.mm"
include "cfv.mm"
include "cmpt.mm"
include "crn.mm"
include "wceq.mm"
include "wrex.mm"
include "lsatset.mm"
include "eleq2d.mm"
include "eqid.mm"
include "fvex.mm"
include "elrnmpti.mm"
include "syl6bb.mm"

theorem islsat
  let vx: setvar x
  let cA: class A
  let cU: class U
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let c.0: class .0.
  let vv: setvar v
  let vw: setvar w
  assume lsatset.v: |- V = ( Base ` W )
  assume lsatset.n: |- N = ( LSpan ` W )
  assume lsatset.z: |- .0. = ( 0g ` W )
  assume lsatset.a: |- A = ( LSAtoms ` W )

  disjoint W x
  disjoint X x
  disjoint N x
  disjoint U x
  disjoint V x
  disjoint .0. x
  disjoint v w
  disjoint N v
  disjoint N w
  disjoint V v
  disjoint V w
  disjoint v x
  disjoint W v
  disjoint w x
  disjoint W w
  disjoint .0. v
  disjoint .0. w
  disjoint X v
  disjoint U v
  assert |- ( W e. X -> ( U e. A <-> E. x e. ( V \ { .0. } ) U = ( N ` { x } ) ) )

  proof
    cW
    cX
    wcel
    #
    cU
    cA
    wcel
    cU
    vx
    cV
    c.0
    csn
    cdif
    #
    vx
    cv
    csn
    #
    cN
    cfv
    #
    cmpt
    #
    crn
    #
    wcel
    cU
    @3
    wceq
    vx
    @1
    wrex
    @0
    cA
    @5
    cU
    vx
    cA
    cN
    cV
    cW
    cX
    c.0
    lsatset.v
    lsatset.n
    lsatset.z
    lsatset.a
    lsatset
    eleq2d
    vx
    @1
    @3
    cU
    @4
    @4
    eqid
    @2
    cN
    fvex
    elrnmpti
    syl6bb
end
