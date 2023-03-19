include "cn.mm"
include "wcel.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "c1.mm"
include "caddc.mm"
include "wn.mm"
include "wb.mm"
include "nneo.mm"
include "ax-mp.mm"

theorem nneoi
  let cN: class N
  let vj: setvar j
  let vk: setvar k
  assume nneoi.1: |- N e. NN


  assert |- ( ( N / 2 ) e. NN <-> -. ( ( N + 1 ) / 2 ) e. NN )

  proof
    cN
    cn
    wcel
    cN
    c2
    cdiv
    co
    cn
    wcel
    cN
    c1
    caddc
    co
    c2
    cdiv
    co
    cn
    wcel
    wn
    wb
    nneoi.1
    cN
    nneo
    ax-mp
end
