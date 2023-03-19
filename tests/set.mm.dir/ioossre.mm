include "cioo.mm"
include "co.mm"
include "cr.mm"
include "cv.mm"
include "elioore.mm"
include "ssriv.mm"

theorem ioossre
  let cA: class A
  let cB: class B
  let vx: setvar x


  assert |- ( A (,) B ) C_ RR

  proof
    vx
    cA
    cB
    cioo
    co
    cr
    vx
    cv
    cA
    cB
    elioore
    ssriv
end
