include "weq.mm"
include "equcomi.mm"
include "impbii.mm"

theorem equcom
  let vx: setvar x
  let vy: setvar y


  assert |- ( x = y <-> y = x )

  proof
    vx
    vy
    weq
    vy
    vx
    weq
    vx
    vy
    equcomi
    vy
    vx
    equcomi
    impbii
end
