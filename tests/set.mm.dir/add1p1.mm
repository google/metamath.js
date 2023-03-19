include "cc.mm"
include "wcel.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "c2.mm"
include "id.mm"
include "1cnd.mm"
include "addassd.mm"
include "wceq.mm"
include "1p1e2.mm"
include "a1i.mm"
include "oveq2d.mm"
include "eqtrd.mm"

theorem add1p1
  let cN: class N


  assert |- ( N e. CC -> ( ( N + 1 ) + 1 ) = ( N + 2 ) )

  proof
    cN
    cc
    wcel
    #
    cN
    c1
    caddc
    co
    c1
    caddc
    co
    cN
    c1
    c1
    caddc
    co
    #
    caddc
    co
    cN
    c2
    caddc
    co
    @0
    cN
    c1
    c1
    @0
    id
    @0
    1cnd
    #
    @2
    addassd
    @0
    @1
    c2
    cN
    caddc
    @1
    c2
    wceq
    @0
    1p1e2
    a1i
    oveq2d
    eqtrd
end
