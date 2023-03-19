include "cv.mm"
include "wbr.mm"
include "wa.mm"
include "copab.mm"
include "wcel.mm"
include "simpl.mm"
include "ssopab2i.mm"
include "sseli.mm"
include "elopabr.mm"
include "syl.mm"

theorem elopabran
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cR: class R

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint R x
  disjoint R y
  assert |- ( A e. { <. x , y >. | ( x R y /\ ps ) } -> A e. R )

  proof
    cA
    vx
    cv
    vy
    cv
    cR
    wbr
    #
    wps
    wa
    #
    vx
    vy
    copab
    #
    wcel
    cA
    @0
    vx
    vy
    copab
    #
    wcel
    cA
    cR
    wcel
    @2
    @3
    cA
    @1
    @0
    vx
    vy
    @0
    wps
    simpl
    ssopab2i
    sseli
    vx
    vy
    cA
    cR
    elopabr
    syl
end
