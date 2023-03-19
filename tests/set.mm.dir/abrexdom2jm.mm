include "cv.mm"
include "wceq.mm"
include "wmo.mm"
include "wcel.mm"
include "moeq.mm"
include "a1i.mm"
include "abrexdomjm.mm"

theorem abrexdom2jm
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cV: class V

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint B x
  assert |- ( A e. V -> { x | E. y e. A x = B } ~<_ A )

  proof
    vx
    cv
    cB
    wceq
    #
    vx
    vy
    cA
    cV
    @0
    vx
    wmo
    vy
    cv
    cA
    wcel
    vx
    cB
    moeq
    a1i
    abrexdomjm
end
