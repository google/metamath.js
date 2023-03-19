include "c0.mm"
include "cv.mm"
include "wcel.mm"
include "wceq.mm"
include "wa.mm"
include "copab.mm"
include "cmpt.mm"
include "0neqopab.mm"
include "df-mpt.mm"
include "eqcomi.mm"
include "eleq2i.mm"
include "mtbi.mm"

theorem bj-0nelmpt
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vy: setvar y


  assert |- -. (/) e. ( x e. A |-> B )

  proof
    c0
    vx
    cv
    cA
    wcel
    vy
    cv
    cB
    wceq
    wa
    #
    vx
    vy
    copab
    #
    wcel
    c0
    vx
    cA
    cB
    cmpt
    #
    wcel
    @0
    vx
    vy
    0neqopab
    @1
    @2
    c0
    @2
    @1
    vx
    vy
    cA
    cB
    df-mpt
    eqcomi
    eleq2i
    mtbi
end
