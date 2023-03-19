include "weq.mm"
include "equcomi.mm"
include "impbii.mm"

theorem equcom
  param vx: setvar x
  param vy: setvar y


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
