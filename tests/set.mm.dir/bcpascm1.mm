include "cn.mm"
include "wcel.mm"
include "cz.mm"
include "wa.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cbc.mm"
include "caddc.mm"
include "cn0.mm"
include "wceq.mm"
include "nnm1nn0.mm"
include "bcpasc.mm"
include "sylan.mm"
include "cc.mm"
include "nncn.mm"
include "npcan1.mm"
include "syl.mm"
include "adantr.mm"
include "oveq1d.mm"
include "eqtrd.mm"

theorem bcpascm1
  let cK: class K
  let cN: class N
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( N e. NN /\ K e. ZZ ) -> ( ( ( N - 1 ) _C K ) + ( ( N - 1 ) _C ( K - 1 ) ) ) = ( N _C K ) )

  proof
    cN
    cn
    wcel
    #
    cK
    cz
    wcel
    #
    wa
    #
    cN
    c1
    cmin
    co
    #
    cK
    cbc
    co
    @3
    cK
    c1
    cmin
    co
    cbc
    co
    caddc
    co
    #
    @3
    c1
    caddc
    co
    #
    cK
    cbc
    co
    #
    cN
    cK
    cbc
    co
    @0
    @3
    cn0
    wcel
    @1
    @4
    @6
    wceq
    cN
    nnm1nn0
    cK
    @3
    bcpasc
    sylan
    @2
    @5
    cN
    cK
    cbc
    @0
    @5
    cN
    wceq
    #
    @1
    @0
    cN
    cc
    wcel
    @7
    cN
    nncn
    cN
    npcan1
    syl
    adantr
    oveq1d
    eqtrd
end
