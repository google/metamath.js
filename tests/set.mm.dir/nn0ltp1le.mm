include "cn0.mm"
include "wcel.mm"
include "cz.mm"
include "clt.mm"
include "wbr.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cle.mm"
include "wb.mm"
include "nn0z.mm"
include "zltp1le.mm"
include "syl2an.mm"

theorem nn0ltp1le
  let cM: class M
  let cN: class N


  assert |- ( ( M e. NN0 /\ N e. NN0 ) -> ( M < N <-> ( M + 1 ) <_ N ) )

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
    c1
    caddc
    co
    cN
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
    zltp1le
    syl2an
end
