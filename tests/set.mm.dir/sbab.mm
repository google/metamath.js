include "weq.mm"
include "cv.mm"
include "wcel.mm"
include "wsb.mm"
include "sbequ12.mm"
include "abbi2dv.mm"

theorem sbab
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A

  disjoint A z
  disjoint x z
  disjoint y z
  assert |- ( x = y -> A = { z | [ y / x ] z e. A } )

  proof
    vx
    vy
    weq
    vz
    cv
    cA
    wcel
    #
    vx
    vy
    wsb
    vz
    cA
    @0
    vx
    vy
    sbequ12
    abbi2dv
end
