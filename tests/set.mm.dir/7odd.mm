include "c7.mm"
include "c6.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "codd.mm"
include "df-7.mm"
include "ceven.mm"
include "wcel.mm"
include "6even.mm"
include "evenp1odd.mm"
include "ax-mp.mm"
include "eqeltri.mm"

theorem 7odd
  let vk: setvar k
  let vx: setvar x


  assert |- 7 e. Odd

  proof
    c7
    c6
    c1
    caddc
    co
    #
    codd
    df-7
    c6
    ceven
    wcel
    @0
    codd
    wcel
    6even
    c6
    evenp1odd
    ax-mp
    eqeltri
end
