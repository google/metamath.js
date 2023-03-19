include "cn0.mm"
include "wcel.mm"
include "cz.mm"
include "cle.mm"
include "wbr.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "clt.mm"
include "wb.mm"
include "nn0z.mm"
include "zleltp1.mm"
include "syl2an.mm"

theorem nn0leltp1
  let cM: class M
  let cN: class N


  assert |- ( ( M e. NN0 /\ N e. NN0 ) -> ( M <_ N <-> M < ( N + 1 ) ) )

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
    cle
    wbr
    cM
    cN
    c1
    caddc
    co
    clt
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
    zleltp1
    syl2an
end
