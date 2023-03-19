include "cn.mm"
include "wcel.mm"
include "cc0.mm"
include "cn0.mm"
include "cz.mm"
include "clt.mm"
include "wbr.mm"
include "wo.mm"
include "cbc.mm"
include "co.mm"
include "wceq.mm"
include "0nn0.mm"
include "a1i.mm"
include "nnz.mm"
include "nngt0.mm"
include "olcd.mm"
include "bcval4.mm"
include "syl3anc.mm"

theorem bc0k
  let cK: class K


  assert |- ( K e. NN -> ( 0 _C K ) = 0 )

  proof
    cK
    cn
    wcel
    #
    cc0
    cn0
    wcel
    #
    cK
    cz
    wcel
    cK
    cc0
    clt
    wbr
    #
    cc0
    cK
    clt
    wbr
    #
    wo
    cc0
    cK
    cbc
    co
    cc0
    wceq
    @1
    @0
    0nn0
    a1i
    cK
    nnz
    @0
    @3
    @2
    cK
    nngt0
    olcd
    cK
    cc0
    bcval4
    syl3anc
end
