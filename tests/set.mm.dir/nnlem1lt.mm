include "cn.mm"
include "wcel.mm"
include "cz.mm"
include "cle.mm"
include "wbr.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "clt.mm"
include "wb.mm"
include "nnz.mm"
include "zlem1lt.mm"
include "syl2an.mm"

theorem nnlem1lt
  let cM: class M
  let cN: class N


  assert |- ( ( M e. NN /\ N e. NN ) -> ( M <_ N <-> ( M - 1 ) < N ) )

  proof
    cM
    cn
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
    cn
    wcel
    cM
    nnz
    cN
    nnz
    cM
    cN
    zlem1lt
    syl2an
end
