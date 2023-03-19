include "c2.mm"
include "caddc.mm"
include "co.mm"
include "c3.mm"
include "c4.mm"
include "c7.mm"
include "2p2e4.mm"
include "oveq1i.mm"
include "4p3e7.mm"
include "eqtr2i.mm"

theorem gbpart7
  let vk: setvar k
  let vx: setvar x


  assert |- 7 = ( ( 2 + 2 ) + 3 )

  proof
    c2
    c2
    caddc
    co
    #
    c3
    caddc
    co
    c4
    c3
    caddc
    co
    c7
    @0
    c4
    c3
    caddc
    2p2e4
    oveq1i
    4p3e7
    eqtr2i
end
