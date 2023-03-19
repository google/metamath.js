include "cc0.mm"
include "ceven.mm"
include "wcel.mm"
include "cz.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "0z.mm"
include "2cn.mm"
include "2ne0.mm"
include "div0i.mm"
include "eqeltri.mm"
include "iseven.mm"
include "mpbir2an.mm"

theorem 0evenALTV
  let vk: setvar k
  let vx: setvar x


  assert |- 0 e. Even

  proof
    cc0
    ceven
    wcel
    cc0
    cz
    wcel
    cc0
    c2
    cdiv
    co
    #
    cz
    wcel
    0z
    @0
    cc0
    cz
    c2
    2cn
    2ne0
    div0i
    0z
    eqeltri
    cc0
    iseven
    mpbir2an
end
