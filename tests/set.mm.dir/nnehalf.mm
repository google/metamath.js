include "cn.mm"
include "wcel.mm"
include "c2.mm"
include "cdvds.mm"
include "wbr.mm"
include "wa.mm"
include "cdiv.mm"
include "co.mm"
include "cn0.mm"
include "nnnn0.mm"
include "nn0ehalf.mm"
include "sylan.mm"
include "wb.mm"
include "nn0enne.mm"
include "adantr.mm"
include "mpbid.mm"

theorem nnehalf
  let cN: class N


  assert |- ( ( N e. NN /\ 2 || N ) -> ( N / 2 ) e. NN )

  proof
    cN
    cn
    wcel
    #
    c2
    cN
    cdvds
    wbr
    #
    wa
    cN
    c2
    cdiv
    co
    #
    cn0
    wcel
    #
    @2
    cn
    wcel
    #
    @0
    cN
    cn0
    wcel
    @1
    @3
    cN
    nnnn0
    cN
    nn0ehalf
    sylan
    @0
    @3
    @4
    wb
    @1
    cN
    nn0enne
    adantr
    mpbid
end
