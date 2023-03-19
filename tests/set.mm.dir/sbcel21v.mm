include "cvv.mm"
include "wcel.mm"
include "cv.mm"
include "wsbc.mm"
include "sbcex.mm"
include "sbcel2gv.mm"
include "biimpd.mm"
include "mpcom.mm"

theorem sbcel21v
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vy: setvar y

  disjoint A x
  disjoint B y
  disjoint x y
  disjoint A y
  assert |- ( [. B / x ]. A e. x -> A e. B )

  proof
    cB
    cvv
    wcel
    #
    cA
    vx
    cv
    wcel
    #
    vx
    cB
    wsbc
    #
    cA
    cB
    wcel
    #
    @1
    vx
    cB
    sbcex
    @0
    @2
    @3
    vx
    cA
    cB
    cvv
    sbcel2gv
    biimpd
    mpcom
end
