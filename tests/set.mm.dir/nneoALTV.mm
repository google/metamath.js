include "cn.mm"
include "wcel.mm"
include "cz.mm"
include "ceven.mm"
include "codd.mm"
include "wn.mm"
include "wb.mm"
include "nnz.mm"
include "zeo2ALTV.mm"
include "syl.mm"

theorem nneoALTV
  let cN: class N
  let vk: setvar k
  let vx: setvar x


  assert |- ( N e. NN -> ( N e. Even <-> -. N e. Odd ) )

  proof
    cN
    cn
    wcel
    cN
    cz
    wcel
    cN
    ceven
    wcel
    cN
    codd
    wcel
    wn
    wb
    cN
    nnz
    cN
    zeo2ALTV
    syl
end
