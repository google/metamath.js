include "weq.mm"
include "wi.mm"
include "wsb.mm"
include "sb2.mm"
include "equcomi.mm"
include "mpg.mm"

theorem equsb2
  let vx: setvar x
  let vy: setvar y


  assert |- [ y / x ] y = x

  proof
    vx
    vy
    weq
    vy
    vx
    weq
    #
    wi
    @0
    vx
    vy
    wsb
    vx
    @0
    vx
    vy
    sb2
    vx
    vy
    equcomi
    mpg
end
