include "c6.mm"
include "ceven.mm"
include "wcel.mm"
include "cz.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "6nn.mm"
include "nnzi.mm"
include "c3.mm"
include "cmul.mm"
include "3t2e6.mm"
include "eqcomi.mm"
include "oveq1i.mm"
include "3cn.mm"
include "2cn.mm"
include "2ne0.mm"
include "divcan4i.mm"
include "eqtri.mm"
include "3z.mm"
include "eqeltri.mm"
include "iseven.mm"
include "mpbir2an.mm"

theorem 6even
  let vk: setvar k
  let vx: setvar x


  assert |- 6 e. Even

  proof
    c6
    ceven
    wcel
    c6
    cz
    wcel
    c6
    c2
    cdiv
    co
    #
    cz
    wcel
    c6
    6nn
    nnzi
    @0
    c3
    cz
    @0
    c3
    c2
    cmul
    co
    #
    c2
    cdiv
    co
    c3
    c6
    @1
    c2
    cdiv
    @1
    c6
    3t2e6
    eqcomi
    oveq1i
    c3
    c2
    3cn
    2cn
    2ne0
    divcan4i
    eqtri
    3z
    eqeltri
    c6
    iseven
    mpbir2an
end
