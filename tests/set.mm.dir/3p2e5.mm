include "c3.mm"
include "c2.mm"
include "caddc.mm"
include "co.mm"
include "c4.mm"
include "c1.mm"
include "c5.mm"
include "df-2.mm"
include "oveq2i.mm"
include "3cn.mm"
include "ax-1cn.mm"
include "addassi.mm"
include "eqtr4i.mm"
include "df-4.mm"
include "oveq1i.mm"
include "df-5.mm"

theorem 3p2e5



  assert |- ( 3 + 2 ) = 5

  proof
    c3
    c2
    caddc
    co
    #
    c4
    c1
    caddc
    co
    #
    c5
    @0
    c3
    c1
    caddc
    co
    #
    c1
    caddc
    co
    #
    @1
    @0
    c3
    c1
    c1
    caddc
    co
    #
    caddc
    co
    @3
    c2
    @4
    c3
    caddc
    df-2
    oveq2i
    c3
    c1
    c1
    3cn
    ax-1cn
    ax-1cn
    addassi
    eqtr4i
    c4
    @2
    c1
    caddc
    df-4
    oveq1i
    eqtr4i
    df-5
    eqtr4i
end
