include "c4.mm"
include "ceven.mm"
include "wcel.mm"
include "c5.mm"
include "codd.mm"
include "4even.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "df-5.mm"
include "evenp1odd.mm"
include "syl5eqel.mm"
include "ax-mp.mm"

theorem 5odd
  let vk: setvar k
  let vx: setvar x


  assert |- 5 e. Odd

  proof
    c4
    ceven
    wcel
    #
    c5
    codd
    wcel
    4even
    @0
    c5
    c4
    c1
    caddc
    co
    codd
    df-5
    c4
    evenp1odd
    syl5eqel
    ax-mp
end
