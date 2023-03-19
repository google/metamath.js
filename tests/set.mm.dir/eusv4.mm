include "cvv.mm"
include "wcel.mm"
include "cv.mm"
include "wceq.mm"
include "wrex.mm"
include "weu.mm"
include "wral.mm"
include "wb.mm"
include "reusv2lem3.mm"
include "a1i.mm"
include "mprg.mm"

theorem eusv4
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  assume eusv4.1: |- B e. _V

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  assert |- ( E! x E. y e. A x = B <-> E! x A. y e. A x = B )

  proof
    cB
    cvv
    wcel
    #
    vx
    cv
    cB
    wceq
    #
    vy
    cA
    wrex
    vx
    weu
    @1
    vy
    cA
    wral
    vx
    weu
    wb
    vy
    cA
    vx
    vy
    cA
    cB
    reusv2lem3
    @0
    vy
    cv
    cA
    wcel
    eusv4.1
    a1i
    mprg
end
