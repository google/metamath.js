include "cuni.mm"
include "crn.mm"
include "cv.mm"
include "ciun.mm"
include "uniiun.mm"
include "rneqi.mm"
include "rniun.mm"
include "eqtri.mm"

theorem rnuni
  let vx: setvar x
  let cA: class A
  let vy: setvar y
  let vz: setvar z
  let cB: class B

  disjoint A x
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B y
  disjoint B z
  assert |- ran U. A = U_ x e. A ran x

  proof
    cA
    cuni
    #
    crn
    vx
    cA
    vx
    cv
    #
    ciun
    #
    crn
    vx
    cA
    @1
    crn
    ciun
    @0
    @2
    vx
    cA
    uniiun
    rneqi
    vx
    cA
    @1
    rniun
    eqtri
end
