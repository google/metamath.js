include "cn0.mm"
include "wcel.mm"
include "c1.mm"
include "clt.mm"
include "wbr.mm"
include "cc0.mm"
include "wceq.mm"
include "cn.mm"
include "wo.mm"
include "wi.mm"
include "elnn0.mm"
include "nnnlt1.mm"
include "pm2.21d.mm"
include "ax-1.mm"
include "jaoi.mm"
include "sylbi.mm"
include "0lt1.mm"
include "breq1.mm"
include "mpbiri.mm"
include "impbid1.mm"

theorem nn0lt10b
  let cN: class N


  assert |- ( N e. NN0 -> ( N < 1 <-> N = 0 ) )

  proof
    cN
    cn0
    wcel
    #
    cN
    c1
    clt
    wbr
    #
    cN
    cc0
    wceq
    #
    @0
    cN
    cn
    wcel
    #
    @2
    wo
    @1
    @2
    wi
    #
    cN
    elnn0
    @3
    @4
    @2
    @3
    @1
    @2
    cN
    nnnlt1
    pm2.21d
    @2
    @1
    ax-1
    jaoi
    sylbi
    @2
    @1
    cc0
    c1
    clt
    wbr
    0lt1
    cN
    cc0
    c1
    clt
    breq1
    mpbiri
    impbid1
end
