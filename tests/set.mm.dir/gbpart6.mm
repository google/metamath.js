include "c3.mm"
include "caddc.mm"
include "co.mm"
include "c6.mm"
include "3p3e6.mm"
include "eqcomi.mm"

theorem gbpart6
  let vk: setvar k
  let vx: setvar x


  assert |- 6 = ( 3 + 3 )

  proof
    c3
    c3
    caddc
    co
    c6
    3p3e6
    eqcomi
end
