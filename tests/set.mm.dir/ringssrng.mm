include "crg.mm"
include "crng.mm"
include "cv.mm"
include "ringrng.mm"
include "ssriv.mm"

theorem ringssrng
  let cR: class R
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vk: setvar k


  assert |- Ring C_ Rng

  proof
    vx
    crg
    crng
    vx
    cv
    ringrng
    ssriv
end
