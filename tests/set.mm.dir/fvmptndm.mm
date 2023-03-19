include "cv.mm"
include "wceq.mm"
include "cmpt.mm"
include "wcel.mm"
include "wa.mm"
include "copab.mm"
include "df-mpt.mm"
include "eqtri.mm"
include "fvopab4ndm.mm"

theorem fvmptndm
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cF: class F
  let cX: class X
  let vy: setvar y
  assume fvmptndm.1: |- F = ( x e. A |-> B )

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint B y
  assert |- ( -. X e. A -> ( F ` X ) = (/) )

  proof
    vy
    cv
    cB
    wceq
    #
    vx
    vy
    cA
    cX
    cF
    cF
    vx
    cA
    cB
    cmpt
    vx
    cv
    cA
    wcel
    @0
    wa
    vx
    vy
    copab
    fvmptndm.1
    vx
    vy
    cA
    cB
    df-mpt
    eqtri
    fvopab4ndm
end
