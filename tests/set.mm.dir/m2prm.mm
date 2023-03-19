include "c2.mm"
include "cexp.mm"
include "co.mm"
include "c1.mm"
include "cmin.mm"
include "c3.mm"
include "cprime.mm"
include "c4.mm"
include "sq2.mm"
include "oveq1i.mm"
include "4m1e3.mm"
include "eqtri.mm"
include "3prm.mm"
include "eqeltri.mm"

theorem m2prm
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( 2 ^ 2 ) - 1 ) e. Prime

  proof
    c2
    c2
    cexp
    co
    #
    c1
    cmin
    co
    #
    c3
    cprime
    @1
    c4
    c1
    cmin
    co
    c3
    @0
    c4
    c1
    cmin
    sq2
    oveq1i
    4m1e3
    eqtri
    3prm
    eqeltri
end
