include "cn0.mm"
include "wcel.mm"
include "cz.mm"
include "clt.mm"
include "wbr.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cle.mm"
include "wb.mm"
include "nn0z.mm"
include "zltlem1.mm"
include "syl2an.mm"

theorem nn0ltlem1
  let cM: class M
  let cN: class N


  assert |- ( ( M e. NN0 /\ N e. NN0 ) -> ( M < N <-> M <_ ( N - 1 ) ) )

  proof
    cM
    cn0
    wcel
    cM
    cz
    wcel
    cN
    cz
    wcel
    cM
    cN
    clt
    wbr
    cM
    cN
    c1
    cmin
    co
    cle
    wbr
    wb
    cN
    cn0
    wcel
    cM
    nn0z
    cN
    nn0z
    cM
    cN
    zltlem1
    syl2an
end
