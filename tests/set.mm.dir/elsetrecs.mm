include "wcel.mm"
include "cv.mm"
include "wss.mm"
include "cfv.mm"
include "wa.mm"
include "wex.mm"
include "elsetrecslem.mm"
include "cvv.mm"
include "vex.mm"
include "a1i.mm"
include "id.mm"
include "setrec1.mm"
include "sselda.mm"
include "exlimiv.mm"
include "impbii.mm"

theorem elsetrecs
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cF: class F
  let va: setvar a
  let vk: setvar k
  assume elsetrecs.1: |- B = setrecs ( F )

  disjoint A x
  disjoint B x
  disjoint F x
  disjoint A a
  disjoint a x
  disjoint B a
  disjoint F a
  disjoint k x
  assert |- ( A e. B <-> E. x ( x C_ B /\ A e. ( F ` x ) ) )

  proof
    cA
    cB
    wcel
    #
    vx
    cv
    #
    cB
    wss
    #
    cA
    @1
    cF
    cfv
    #
    wcel
    wa
    #
    vx
    wex
    vx
    cA
    cB
    cF
    elsetrecs.1
    elsetrecslem
    @4
    @0
    vx
    @2
    @3
    cB
    cA
    @2
    @1
    cB
    cF
    elsetrecs.1
    @1
    cvv
    wcel
    @2
    vx
    vex
    a1i
    @2
    id
    setrec1
    sselda
    exlimiv
    impbii
end
