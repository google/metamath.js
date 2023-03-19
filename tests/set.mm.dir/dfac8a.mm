include "cvv.mm"
include "cv.mm"
include "crn.mm"
include "cdif.mm"
include "cfv.mm"
include "cmpt.mm"
include "crecs.mm"
include "eqid.mm"
include "weq.mm"
include "rneq.mm"
include "difeq2d.mm"
include "fveq2d.mm"
include "cbvmptv.mm"
include "dfac8alem.mm"

theorem dfac8a
  let vy: setvar y
  let cA: class A
  let cB: class B
  let vh: setvar h
  let vf: setvar f
  let vv: setvar v

  disjoint h y
  disjoint A h
  disjoint A y
  disjoint B h
  disjoint f h
  disjoint f v
  disjoint f y
  disjoint A f
  disjoint h v
  disjoint v y
  disjoint A v
  assert |- ( A e. B -> ( E. h A. y e. ~P A ( y =/= (/) -> ( h ` y ) e. y ) -> A e. dom card ) )

  proof
    vy
    cA
    cB
    vf
    vh
    vv
    cvv
    cA
    vv
    cv
    #
    crn
    #
    cdif
    #
    vh
    cv
    #
    cfv
    #
    cmpt
    #
    crecs
    #
    @5
    @6
    eqid
    vv
    vf
    cvv
    @4
    cA
    vf
    cv
    #
    crn
    #
    cdif
    #
    @3
    cfv
    vv
    vf
    weq
    #
    @2
    @9
    @3
    @10
    @1
    @8
    cA
    @0
    @7
    rneq
    difeq2d
    fveq2d
    cbvmptv
    dfac8alem
end
