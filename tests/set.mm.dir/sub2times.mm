include "cc.mm"
include "wcel.mm"
include "c2.mm"
include "cmul.mm"
include "co.mm"
include "cmin.mm"
include "caddc.mm"
include "cneg.mm"
include "2times.mm"
include "oveq2d.mm"
include "id.mm"
include "addcld.mm"
include "negsubd.mm"
include "negdid.mm"
include "negcl.mm"
include "addassd.mm"
include "cc0.mm"
include "negid.mm"
include "oveq1d.mm"
include "addid2d.mm"
include "eqtrd.mm"
include "3eqtr2d.mm"

theorem sub2times
  let cA: class A


  assert |- ( A e. CC -> ( A - ( 2 x. A ) ) = -u A )

  proof
    cA
    cc
    wcel
    #
    cA
    c2
    cA
    cmul
    co
    #
    cmin
    co
    cA
    cA
    cA
    caddc
    co
    #
    cmin
    co
    cA
    @2
    cneg
    #
    caddc
    co
    #
    cA
    cneg
    #
    @0
    @1
    @2
    cA
    cmin
    cA
    2times
    oveq2d
    @0
    cA
    @2
    @0
    id
    #
    @0
    cA
    cA
    @6
    @6
    addcld
    negsubd
    @0
    @4
    cA
    @5
    @5
    caddc
    co
    #
    caddc
    co
    cA
    @5
    caddc
    co
    #
    @5
    caddc
    co
    #
    @5
    @0
    @3
    @7
    cA
    caddc
    @0
    cA
    cA
    @6
    @6
    negdid
    oveq2d
    @0
    cA
    @5
    @5
    @6
    cA
    negcl
    #
    @10
    addassd
    @0
    @9
    cc0
    @5
    caddc
    co
    @5
    @0
    @8
    cc0
    @5
    caddc
    cA
    negid
    oveq1d
    @0
    @5
    @10
    addid2d
    eqtrd
    3eqtr2d
    3eqtr2d
end
