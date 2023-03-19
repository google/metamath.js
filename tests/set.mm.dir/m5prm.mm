include "c2.mm"
include "c5.mm"
include "cexp.mm"
include "co.mm"
include "c1.mm"
include "cmin.mm"
include "c3.mm"
include "cdc.mm"
include "cprime.mm"
include "c4.mm"
include "3nn0.mm"
include "2nn0.mm"
include "1nn0.mm"
include "2exp5.mm"
include "3p1e4.mm"
include "2m1e1.mm"
include "decsubi.mm"
include "31prm.mm"
include "eqeltri.mm"

theorem m5prm
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( 2 ^ 5 ) - 1 ) e. Prime

  proof
    c2
    c5
    cexp
    co
    #
    c1
    cmin
    co
    c3
    c1
    cdc
    cprime
    c3
    c2
    c1
    c4
    @0
    c1
    3nn0
    2nn0
    1nn0
    2exp5
    3p1e4
    2m1e1
    decsubi
    31prm
    eqeltri
end
