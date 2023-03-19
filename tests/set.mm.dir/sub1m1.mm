include "cc.mm"
include "wcel.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "caddc.mm"
include "c2.mm"
include "id.mm"
include "1cnd.mm"
include "subsub4d.mm"
include "wceq.mm"
include "1p1e2.mm"
include "a1i.mm"
include "oveq2d.mm"
include "eqtrd.mm"

theorem sub1m1
  let cN: class N


  assert |- ( N e. CC -> ( ( N - 1 ) - 1 ) = ( N - 2 ) )

  proof
    cN
    cc
    wcel
    #
    cN
    c1
    cmin
    co
    c1
    cmin
    co
    cN
    c1
    c1
    caddc
    co
    #
    cmin
    co
    cN
    c2
    cmin
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
    subsub4d
    @0
    @1
    c2
    cN
    cmin
    @1
    c2
    wceq
    @0
    1p1e2
    a1i
    oveq2d
    eqtrd
end
