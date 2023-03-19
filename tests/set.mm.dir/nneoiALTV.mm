include "cn.mm"
include "wcel.mm"
include "ceven.mm"
include "codd.mm"
include "wn.mm"
include "wb.mm"
include "nneoALTV.mm"
include "ax-mp.mm"

theorem nneoiALTV
  let cN: class N
  let vk: setvar k
  let vx: setvar x
  assume nneoiALTV.1: |- N e. NN


  assert |- ( N e. Even <-> -. N e. Odd )

  proof
    cN
    cn
    wcel
    cN
    ceven
    wcel
    cN
    codd
    wcel
    wn
    wb
    nneoiALTV.1
    cN
    nneoALTV
    ax-mp
end
