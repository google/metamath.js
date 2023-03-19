include "c3.mm"
include "caddc.mm"
include "co.mm"
include "c6.mm"
include "c9.mm"
include "3p3e6.mm"
include "oveq1i.mm"
include "6p3e9.mm"
include "eqtr2i.mm"

theorem gbpart9
  let vk: setvar k
  let vx: setvar x


  assert |- 9 = ( ( 3 + 3 ) + 3 )

  proof
    c3
    c3
    caddc
    co
    #
    c3
    caddc
    co
    c6
    c3
    caddc
    co
    c9
    @0
    c6
    c3
    caddc
    3p3e6
    oveq1i
    6p3e9
    eqtr2i
end
