include "weq.mm"
include "equid.mm"
include "nfth.mm"

theorem nfequid
  let vx: setvar x
  let vy: setvar y


  assert |- F/ y x = x

  proof
    vx
    vx
    weq
    vy
    vx
    equid
    nfth
end
