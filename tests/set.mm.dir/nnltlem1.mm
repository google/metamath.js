include "cn.mm"
include "wcel.mm"
include "cz.mm"
include "clt.mm"
include "wbr.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cle.mm"
include "wb.mm"
include "nnz.mm"
include "zltlem1.mm"
include "syl2an.mm"

theorem nnltlem1
  let cM: class M
  let cN: class N


  assert |- ( ( M e. NN /\ N e. NN ) -> ( M < N <-> M <_ ( N - 1 ) ) )

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
    cn
    wcel
    cM
    nnz
    cN
    nnz
    cM
    cN
    zltlem1
    syl2an
end
