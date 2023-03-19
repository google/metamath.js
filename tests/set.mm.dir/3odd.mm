include "c2.mm"
include "ceven.mm"
include "wcel.mm"
include "c3.mm"
include "codd.mm"
include "2evenALTV.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "df-3.mm"
include "evenp1odd.mm"
include "syl5eqel.mm"
include "ax-mp.mm"

theorem 3odd
  let vk: setvar k
  let vx: setvar x


  assert |- 3 e. Odd

  proof
    c2
    ceven
    wcel
    #
    c3
    codd
    wcel
    2evenALTV
    @0
    c3
    c2
    c1
    caddc
    co
    codd
    df-3
    c2
    evenp1odd
    syl5eqel
    ax-mp
end
