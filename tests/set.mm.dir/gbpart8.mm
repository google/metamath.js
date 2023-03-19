include "c3.mm"
include "c5.mm"
include "caddc.mm"
include "co.mm"
include "c8.mm"
include "5cn.mm"
include "3cn.mm"
include "5p3e8.mm"
include "addcomli.mm"
include "eqcomi.mm"

theorem gbpart8
  let vk: setvar k
  let vx: setvar x


  assert |- 8 = ( 3 + 5 )

  proof
    c3
    c5
    caddc
    co
    c8
    c5
    c3
    c8
    5cn
    3cn
    5p3e8
    addcomli
    eqcomi
end
