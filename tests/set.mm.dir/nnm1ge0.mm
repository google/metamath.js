include "cn.mm"
include "wcel.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cle.mm"
include "nngt0.mm"
include "cz.mm"
include "wb.mm"
include "0z.mm"
include "nnz.mm"
include "zltlem1.mm"
include "sylancr.mm"
include "mpbid.mm"

theorem nnm1ge0
  let cN: class N


  assert |- ( N e. NN -> 0 <_ ( N - 1 ) )

  proof
    cN
    cn
    wcel
    #
    cc0
    cN
    clt
    wbr
    #
    cc0
    cN
    c1
    cmin
    co
    cle
    wbr
    #
    cN
    nngt0
    @0
    cc0
    cz
    wcel
    cN
    cz
    wcel
    @1
    @2
    wb
    0z
    cN
    nnz
    cc0
    cN
    zltlem1
    sylancr
    mpbid
end
