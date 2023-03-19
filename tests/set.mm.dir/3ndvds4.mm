include "c3.mm"
include "c4.mm"
include "c1.mm"
include "3nn.mm"
include "1nn0.mm"
include "1nn.mm"
include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "3t1e3.mm"
include "oveq1i.mm"
include "3p1e4.mm"
include "eqtri.mm"
include "1lt3.mm"
include "ndvdsi.mm"

theorem 3ndvds4
  let vk: setvar k
  let vx: setvar x


  assert |- -. 3 || 4

  proof
    c3
    c4
    c1
    c1
    3nn
    1nn0
    1nn
    c3
    c1
    cmul
    co
    #
    c1
    caddc
    co
    c3
    c1
    caddc
    co
    c4
    @0
    c3
    c1
    caddc
    3t1e3
    oveq1i
    3p1e4
    eqtri
    1lt3
    ndvdsi
end
