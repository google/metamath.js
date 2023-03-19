include "cz.mm"
include "wcel.mm"
include "wa.mm"
include "cc0.mm"
include "wceq.mm"
include "wo.mm"
include "clcm.mm"
include "co.mm"
include "cn0.mm"
include "lcmcom.mm"
include "adantr.mm"
include "oveq2.mm"
include "lcm0val.mm"
include "sylan9eqr.mm"
include "adantll.mm"
include "eqtrd.mm"
include "adantlr.mm"
include "jaodan.mm"
include "0nn0.mm"
include "syl6eqel.mm"
include "wn.mm"
include "lcmn0cl.mm"
include "nnnn0d.mm"
include "pm2.61dan.mm"

theorem lcmcl
  let cM: class M
  let cN: class N


  assert |- ( ( M e. ZZ /\ N e. ZZ ) -> ( M lcm N ) e. NN0 )

  proof
    cM
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    wa
    #
    cM
    cc0
    wceq
    #
    cN
    cc0
    wceq
    #
    wo
    #
    cM
    cN
    clcm
    co
    #
    cn0
    wcel
    @2
    @5
    wa
    @6
    cc0
    cn0
    @2
    @3
    @6
    cc0
    wceq
    #
    @4
    @2
    @3
    wa
    @6
    cN
    cM
    clcm
    co
    #
    cc0
    @2
    @6
    @8
    wceq
    @3
    cM
    cN
    lcmcom
    adantr
    @1
    @3
    @8
    cc0
    wceq
    @0
    @3
    @1
    @8
    cN
    cc0
    clcm
    co
    cc0
    cM
    cc0
    cN
    clcm
    oveq2
    cN
    lcm0val
    sylan9eqr
    adantll
    eqtrd
    @0
    @4
    @7
    @1
    @4
    @0
    @6
    cM
    cc0
    clcm
    co
    cc0
    cN
    cc0
    cM
    clcm
    oveq2
    cM
    lcm0val
    sylan9eqr
    adantlr
    jaodan
    0nn0
    syl6eqel
    @2
    @5
    wn
    wa
    @6
    cM
    cN
    lcmn0cl
    nnnn0d
    pm2.61dan
end
