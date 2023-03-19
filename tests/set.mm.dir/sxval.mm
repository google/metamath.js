include "wcel.mm"
include "wa.mm"
include "csx.mm"
include "co.mm"
include "cv.mm"
include "cxp.mm"
include "cmpt2.mm"
include "crn.mm"
include "csigagen.mm"
include "cfv.mm"
include "cvv.mm"
include "wceq.mm"
include "elex.mm"
include "id.mm"
include "eqidd.mm"
include "mpt2eq123dv.mm"
include "rneqd.mm"
include "fveq2d.mm"
include "df-sx.mm"
include "fvex.mm"
include "ovmpt2.mm"
include "syl2an.mm"
include "fveq2i.mm"
include "syl6eqr.mm"

theorem sxval
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cS: class S
  let cT: class T
  let cV: class V
  let cW: class W
  let vs: setvar s
  let vt: setvar t
  assume sxval.1: |- A = ran ( x e. S , y e. T |-> ( x X. y ) )

  disjoint x y
  disjoint S x
  disjoint S y
  disjoint T x
  disjoint T y
  disjoint s t
  disjoint s x
  disjoint s y
  disjoint S s
  disjoint t x
  disjoint t y
  disjoint S t
  disjoint T s
  disjoint T t
  assert |- ( ( S e. V /\ T e. W ) -> ( S sX T ) = ( sigaGen ` A ) )

  proof
    cS
    cV
    wcel
    #
    cT
    cW
    wcel
    #
    wa
    cS
    cT
    csx
    co
    #
    vx
    vy
    cS
    cT
    vx
    cv
    vy
    cv
    cxp
    #
    cmpt2
    #
    crn
    #
    csigagen
    cfv
    #
    cA
    csigagen
    cfv
    @0
    cS
    cvv
    wcel
    cT
    cvv
    wcel
    @2
    @6
    wceq
    @1
    cS
    cV
    elex
    cT
    cW
    elex
    vs
    vt
    cS
    cT
    cvv
    cvv
    vx
    vy
    vs
    cv
    #
    vt
    cv
    #
    @3
    cmpt2
    #
    crn
    #
    csigagen
    cfv
    @6
    csx
    vx
    vy
    cS
    @8
    @3
    cmpt2
    #
    crn
    #
    csigagen
    cfv
    @7
    cS
    wceq
    #
    @10
    @12
    csigagen
    @13
    @9
    @11
    @13
    vx
    vy
    @7
    @8
    @3
    cS
    @8
    @3
    @13
    id
    @13
    @8
    eqidd
    @13
    @3
    eqidd
    mpt2eq123dv
    rneqd
    fveq2d
    @8
    cT
    wceq
    #
    @12
    @5
    csigagen
    @14
    @11
    @4
    @14
    vx
    vy
    cS
    @8
    @3
    cS
    cT
    @3
    @14
    cS
    eqidd
    @14
    id
    @14
    @3
    eqidd
    mpt2eq123dv
    rneqd
    fveq2d
    vx
    vy
    vt
    vs
    df-sx
    @5
    csigagen
    fvex
    ovmpt2
    syl2an
    cA
    @5
    csigagen
    sxval.1
    fveq2i
    syl6eqr
end
