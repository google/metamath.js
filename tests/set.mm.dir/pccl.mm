include "cn.mm"
include "wcel.mm"
include "cprime.mm"
include "cz.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "cpc.mm"
include "co.mm"
include "cn0.mm"
include "nnz.mm"
include "nnne0.mm"
include "jca.mm"
include "pczcl.mm"
include "sylan2.mm"

theorem pccl
  let cP: class P
  let cN: class N


  assert |- ( ( P e. Prime /\ N e. NN ) -> ( P pCnt N ) e. NN0 )

  proof
    cN
    cn
    wcel
    #
    cP
    cprime
    wcel
    cN
    cz
    wcel
    #
    cN
    cc0
    wne
    #
    wa
    cP
    cN
    cpc
    co
    cn0
    wcel
    @0
    @1
    @2
    cN
    nnz
    cN
    nnne0
    jca
    cP
    cN
    pczcl
    sylan2
end
