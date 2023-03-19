include "cv.mm"
include "cid.mm"
include "weq.mm"
include "id.mm"
include "dfid3.mm"
include "eqer.mm"

theorem ider
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- _I Er _V

  proof
    vx
    vy
    vx
    cv
    vy
    cv
    cid
    vx
    vy
    weq
    id
    vx
    vy
    dfid3
    eqer
end
