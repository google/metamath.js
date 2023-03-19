include "codd.mm"
include "wcel.mm"
include "cc0.mm"
include "cbits.mm"
include "cfv.mm"
include "cz.mm"
include "wb.mm"
include "oddz.mm"
include "bits0ALTV.mm"
include "syl.mm"
include "ibir.mm"

theorem bits0oALTV
  let cN: class N
  let vk: setvar k
  let vx: setvar x


  assert |- ( N e. Odd -> 0 e. ( bits ` N ) )

  proof
    cN
    codd
    wcel
    #
    cc0
    cN
    cbits
    cfv
    wcel
    #
    @0
    cN
    cz
    wcel
    @1
    @0
    wb
    cN
    oddz
    cN
    bits0ALTV
    syl
    ibir
end
