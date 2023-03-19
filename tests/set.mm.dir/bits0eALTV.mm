include "ceven.mm"
include "wcel.mm"
include "cc0.mm"
include "cbits.mm"
include "cfv.mm"
include "codd.mm"
include "evennodd.mm"
include "cz.mm"
include "wb.mm"
include "evenz.mm"
include "bits0ALTV.mm"
include "syl.mm"
include "mtbird.mm"

theorem bits0eALTV
  let cN: class N
  let vk: setvar k
  let vx: setvar x


  assert |- ( N e. Even -> -. 0 e. ( bits ` N ) )

  proof
    cN
    ceven
    wcel
    #
    cc0
    cN
    cbits
    cfv
    wcel
    #
    cN
    codd
    wcel
    #
    cN
    evennodd
    @0
    cN
    cz
    wcel
    @1
    @2
    wb
    cN
    evenz
    cN
    bits0ALTV
    syl
    mtbird
end
