include "weq.mm"
include "wi.mm"
include "wsb.mm"
include "bj-sb2v.mm"
include "id.mm"
include "mpg.mm"

theorem bj-equsb1v
  let vx: setvar x
  let vy: setvar y

  disjoint x y
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
    bj-sb2v
    @0
    id
    mpg
end
