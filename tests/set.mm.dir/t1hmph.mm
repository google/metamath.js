include "ct1.mm"
include "t1top.mm"
include "cv.mm"
include "cuni.mm"
include "cnt1.mm"
include "haushmphlem.mm"

theorem t1hmph
  let cJ: class J
  let cK: class K
  let vf: setvar f
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( J ~= K -> ( J e. Fre -> K e. Fre ) )

  proof
    ct1
    vf
    cJ
    cK
    cJ
    t1top
    vf
    cv
    cK
    cJ
    cK
    cuni
    cJ
    cuni
    cnt1
    haushmphlem
end
