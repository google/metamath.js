include "c3.mm"
include "codd.mm"
include "wcel.mm"
include "c4.mm"
include "ceven.mm"
include "3odd.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "df-4.mm"
include "oddp1eveni.mm"
include "syl5eqel.mm"
include "ax-mp.mm"

theorem 4even
  let vk: setvar k
  let vx: setvar x


  assert |- 4 e. Even

  proof
    c3
    codd
    wcel
    #
    c4
    ceven
    wcel
    3odd
    @0
    c4
    c3
    c1
    caddc
    co
    ceven
    df-4
    c3
    oddp1eveni
    syl5eqel
    ax-mp
end
