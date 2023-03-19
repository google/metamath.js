include "cc.mm"
include "wcel.mm"
include "c2.mm"
include "cmin.mm"
include "co.mm"
include "c1.mm"
include "caddc.mm"
include "c3.mm"
include "id.mm"
include "2cnd.mm"
include "1cnd.mm"
include "subsub4d.mm"
include "wceq.mm"
include "2p1e3.mm"
include "a1i.mm"
include "oveq2d.mm"
include "eqtrd.mm"

theorem cnm2m1cnm3
  let cA: class A


  assert |- ( A e. CC -> ( ( A - 2 ) - 1 ) = ( A - 3 ) )

  proof
    cA
    cc
    wcel
    #
    cA
    c2
    cmin
    co
    c1
    cmin
    co
    cA
    c2
    c1
    caddc
    co
    #
    cmin
    co
    cA
    c3
    cmin
    co
    @0
    cA
    c2
    c1
    @0
    id
    @0
    2cnd
    @0
    1cnd
    subsub4d
    @0
    @1
    c3
    cA
    cmin
    @1
    c3
    wceq
    @0
    2p1e3
    a1i
    oveq2d
    eqtrd
end
