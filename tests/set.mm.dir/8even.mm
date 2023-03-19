include "c8.mm"
include "ceven.mm"
include "wcel.mm"
include "cz.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "8nn.mm"
include "nnzi.mm"
include "c4.mm"
include "cmul.mm"
include "4t2e8.mm"
include "eqcomi.mm"
include "oveq1i.mm"
include "4cn.mm"
include "2cn.mm"
include "2ne0.mm"
include "divcan4i.mm"
include "eqtri.mm"
include "4z.mm"
include "eqeltri.mm"
include "iseven.mm"
include "mpbir2an.mm"

theorem 8even
  let vk: setvar k
  let vx: setvar x


  assert |- 8 e. Even

  proof
    c8
    ceven
    wcel
    c8
    cz
    wcel
    c8
    c2
    cdiv
    co
    #
    cz
    wcel
    c8
    8nn
    nnzi
    @0
    c4
    cz
    @0
    c4
    c2
    cmul
    co
    #
    c2
    cdiv
    co
    c4
    c8
    @1
    c2
    cdiv
    @1
    c8
    4t2e8
    eqcomi
    oveq1i
    c4
    c2
    4cn
    2cn
    2ne0
    divcan4i
    eqtri
    4z
    eqeltri
    c8
    iseven
    mpbir2an
end
