include "cn0.mm"
include "wcel.mm"
include "cz.mm"
include "cle.mm"
include "wbr.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "clt.mm"
include "wb.mm"
include "nn0z.mm"
include "zlem1lt.mm"
include "syl2an.mm"

theorem nn0lem1lt
  let cM: class M
  let cN: class N


  assert |- ( ( M e. NN0 /\ N e. NN0 ) -> ( M <_ N <-> ( M - 1 ) < N ) )

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
    c1
    cmin
    co
    cN
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
    zlem1lt
    syl2an
end
