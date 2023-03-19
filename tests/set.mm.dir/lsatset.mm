include "wcel.mm"
include "clsa.mm"
include "cfv.mm"
include "csn.mm"
include "cdif.mm"
include "cv.mm"
include "cmpt.mm"
include "crn.mm"
include "cvv.mm"
include "wceq.mm"
include "elex.mm"
include "cbs.mm"
include "c0g.mm"
include "clspn.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "sneqd.mm"
include "difeq12d.mm"
include "fveq1d.mm"
include "mpteq12dv.mm"
include "rneqd.mm"
include "df-lsatoms.mm"
include "c0.mm"
include "cun.mm"
include "fvex.mm"
include "eqeltri.mm"
include "rnex.mm"
include "p0ex.mm"
include "unex.mm"
include "wf.mm"
include "wss.mm"
include "eqid.mm"
include "fvrn0.mm"
include "a1i.mm"
include "fmpti.mm"
include "frn.mm"
include "ax-mp.mm"
include "ssexi.mm"
include "fvmpt.mm"
include "syl.mm"
include "syl5eq.mm"

theorem lsatset
  let vv: setvar v
  let cA: class A
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let c.0: class .0.
  let vw: setvar w
  let vx: setvar x
  assume lsatset.v: |- V = ( Base ` W )
  assume lsatset.n: |- N = ( LSpan ` W )
  assume lsatset.z: |- .0. = ( 0g ` W )
  assume lsatset.a: |- A = ( LSAtoms ` W )

  disjoint N v
  disjoint V v
  disjoint W v
  disjoint .0. v
  disjoint X v
  disjoint v w
  disjoint N w
  disjoint V w
  disjoint v x
  disjoint w x
  disjoint W w
  disjoint W x
  disjoint .0. w
  disjoint X x
  assert |- ( W e. X -> A = ran ( v e. ( V \ { .0. } ) |-> ( N ` { v } ) ) )

  proof
    cW
    cX
    wcel
    #
    cA
    cW
    clsa
    cfv
    #
    vv
    cV
    c.0
    csn
    #
    cdif
    #
    vv
    cv
    #
    csn
    #
    cN
    cfv
    #
    cmpt
    #
    crn
    #
    lsatset.a
    @0
    cW
    cvv
    wcel
    @1
    @8
    wceq
    cW
    cX
    elex
    vw
    cW
    vv
    vw
    cv
    #
    cbs
    cfv
    #
    @9
    c0g
    cfv
    #
    csn
    #
    cdif
    #
    @5
    @9
    clspn
    cfv
    #
    cfv
    #
    cmpt
    #
    crn
    @8
    cvv
    clsa
    @9
    cW
    wceq
    #
    @16
    @7
    @17
    vv
    @13
    @15
    @3
    @6
    @17
    @10
    cV
    @12
    @2
    @17
    @10
    cW
    cbs
    cfv
    cV
    @9
    cW
    cbs
    fveq2
    lsatset.v
    syl6eqr
    @17
    @11
    c.0
    @17
    @11
    cW
    c0g
    cfv
    c.0
    @9
    cW
    c0g
    fveq2
    lsatset.z
    syl6eqr
    sneqd
    difeq12d
    @17
    @5
    @14
    cN
    @17
    @14
    cW
    clspn
    cfv
    #
    cN
    @9
    cW
    clspn
    fveq2
    lsatset.n
    syl6eqr
    fveq1d
    mpteq12dv
    rneqd
    vw
    vv
    df-lsatoms
    @8
    cN
    crn
    #
    c0
    csn
    #
    cun
    #
    @19
    @20
    cN
    cN
    @18
    cvv
    lsatset.n
    cW
    clspn
    fvex
    eqeltri
    rnex
    p0ex
    unex
    @3
    @21
    @7
    wf
    @8
    @21
    wss
    vv
    @3
    @21
    @6
    @7
    @7
    eqid
    @6
    @21
    wcel
    @4
    @3
    wcel
    cN
    @5
    fvrn0
    a1i
    fmpti
    @3
    @21
    @7
    frn
    ax-mp
    ssexi
    fvmpt
    syl
    syl5eq
end
