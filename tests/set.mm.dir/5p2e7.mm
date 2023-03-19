include "c5.mm"
include "c2.mm"
include "caddc.mm"
include "co.mm"
include "c6.mm"
include "c1.mm"
include "c7.mm"
include "df-2.mm"
include "oveq2i.mm"
include "5cn.mm"
include "ax-1cn.mm"
include "addassi.mm"
include "eqtr4i.mm"
include "df-6.mm"
include "oveq1i.mm"
include "df-7.mm"

theorem 5p2e7



  assert |- ( 5 + 2 ) = 7

  proof
    c5
    c2
    caddc
    co
    #
    c6
    c1
    caddc
    co
    #
    c7
    @0
    c5
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
    c5
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
    c5
    caddc
    df-2
    oveq2i
    c5
    c1
    c1
    5cn
    ax-1cn
    ax-1cn
    addassi
    eqtr4i
    c6
    @2
    c1
    caddc
    df-6
    oveq1i
    eqtr4i
    df-7
    eqtr4i
end
