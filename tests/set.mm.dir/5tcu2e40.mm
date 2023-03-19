include "c5.mm"
include "c2.mm"
include "c3.mm"
include "cexp.mm"
include "co.mm"
include "cmul.mm"
include "c8.mm"
include "c4.mm"
include "cc0.mm"
include "cdc.mm"
include "cu2.mm"
include "oveq2i.mm"
include "5cn.mm"
include "8cn.mm"
include "mulcomi.mm"
include "8t5e40.mm"
include "3eqtri.mm"

theorem 5tcu2e40
  let vk: setvar k
  let vx: setvar x


  assert |- ( 5 x. ( 2 ^ 3 ) ) = ; 4 0

  proof
    c5
    c2
    c3
    cexp
    co
    #
    cmul
    co
    c5
    c8
    cmul
    co
    c8
    c5
    cmul
    co
    c4
    cc0
    cdc
    @0
    c8
    c5
    cmul
    cu2
    oveq2i
    c5
    c8
    5cn
    8cn
    mulcomi
    8t5e40
    3eqtri
end
