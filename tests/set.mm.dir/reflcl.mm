include "cr.mm"
include "wcel.mm"
include "cfl.mm"
include "cfv.mm"
include "flcl.mm"
include "zred.mm"

theorem reflcl
  let cA: class A
  let vx: setvar x
  let vy: setvar y


  assert |- ( A e. RR -> ( |_ ` A ) e. RR )

  proof
    cA
    cr
    wcel
    cA
    cfl
    cfv
    cA
    flcl
    zred
end
