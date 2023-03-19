include "weq.mm"
include "hbequid.mm"
include "nf5i.mm"

theorem nfequid-o
  let vx: setvar x
  let vy: setvar y


  assert |- F/ y x = x

  proof
    vx
    vx
    weq
    vy
    vx
    vy
    hbequid
    nf5i
end
