include "c3.mm"
include "caddc.mm"
include "co.mm"
include "c5.mm"
include "c6.mm"
include "c1.mm"
include "cdc.mm"
include "3p3e6.mm"
include "oveq1i.mm"
include "6p5e11.mm"
include "eqtr2i.mm"

theorem gbpart11
  let vk: setvar k
  let vx: setvar x


  assert |- ; 1 1 = ( ( 3 + 3 ) + 5 )

  proof
    c3
    c3
    caddc
    co
    #
    c5
    caddc
    co
    c6
    c5
    caddc
    co
    c1
    c1
    cdc
    @0
    c6
    c5
    caddc
    3p3e6
    oveq1i
    6p5e11
    eqtr2i
end
