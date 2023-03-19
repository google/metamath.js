include "c0.mm"
include "csn.mm"
include "sn0topon.mm"
include "topontopi.mm"

theorem sn0top
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cV: class V


  assert |- { (/) } e. Top

  proof
    c0
    c0
    csn
    sn0topon
    topontopi
end
