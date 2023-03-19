include "cn.mm"
include "wcel.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "cn0.mm"
include "cc0.mm"
include "wceq.mm"
include "wo.mm"
include "wi.mm"
include "elnn0.mm"
include "nncn.mm"
include "2cnd.mm"
include "wne.mm"
include "2ne0.mm"
include "a1i.mm"
include "diveq0ad.mm"
include "eleq1.mm"
include "0nnn.mm"
include "pm2.21i.mm"
include "syl6bi.mm"
include "com12.mm"
include "sylbid.mm"
include "jao1i.mm"
include "sylbi.mm"
include "nnnn0.mm"
include "impbid1.mm"

theorem nn0enne
  let cN: class N


  assert |- ( N e. NN -> ( ( N / 2 ) e. NN0 <-> ( N / 2 ) e. NN ) )

  proof
    cN
    cn
    wcel
    #
    cN
    c2
    cdiv
    co
    #
    cn0
    wcel
    #
    @1
    cn
    wcel
    #
    @2
    @0
    @3
    @2
    @3
    @1
    cc0
    wceq
    #
    wo
    @0
    @3
    wi
    @1
    elnn0
    @3
    @4
    @0
    @0
    @4
    @3
    @0
    @4
    cN
    cc0
    wceq
    #
    @3
    @0
    cN
    c2
    cN
    nncn
    @0
    2cnd
    c2
    cc0
    wne
    @0
    2ne0
    a1i
    diveq0ad
    @5
    @0
    @3
    @5
    @0
    cc0
    cn
    wcel
    #
    @3
    cN
    cc0
    cn
    eleq1
    @6
    @3
    0nnn
    pm2.21i
    syl6bi
    com12
    sylbid
    com12
    jao1i
    sylbi
    com12
    @1
    nnnn0
    impbid1
end
