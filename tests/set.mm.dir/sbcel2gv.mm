include "cv.mm"
include "wcel.mm"
include "eleq2.mm"
include "sbcie2g.mm"

theorem sbcel2gv
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cV: class V
  let vy: setvar y

  disjoint A x
  disjoint B y
  disjoint x y
  disjoint A y
  assert |- ( B e. V -> ( [. B / x ]. A e. x <-> A e. B ) )

  proof
    cA
    vx
    cv
    #
    wcel
    cA
    vy
    cv
    #
    wcel
    cA
    cB
    wcel
    vx
    vy
    cB
    cV
    @0
    @1
    cA
    eleq2
    @1
    cB
    cA
    eleq2
    sbcie2g
end
