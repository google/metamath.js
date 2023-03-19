include "c2.mm"
include "ceven.mm"
include "wcel.mm"
include "cz.mm"
include "cdiv.mm"
include "co.mm"
include "2z.mm"
include "c1.mm"
include "2div2e1.mm"
include "1z.mm"
include "eqeltri.mm"
include "iseven.mm"
include "mpbir2an.mm"

theorem 2evenALTV
  let vk: setvar k
  let vx: setvar x


  assert |- 2 e. Even

  proof
    c2
    ceven
    wcel
    c2
    cz
    wcel
    c2
    c2
    cdiv
    co
    #
    cz
    wcel
    2z
    @0
    c1
    cz
    2div2e1
    1z
    eqeltri
    c2
    iseven
    mpbir2an
end
