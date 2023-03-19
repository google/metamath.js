include "weq.mm"
include "wi.mm"
include "wsb.mm"
include "sb2.mm"
include "id.mm"
include "mpg.mm"

theorem equsb1
  param vx: setvar x
  param vy: setvar y


  assert |- [ y / x ] x = y

  proof
    vx
    vy
    weq
    #
    @0
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
    @0
    id
    mpg
end
