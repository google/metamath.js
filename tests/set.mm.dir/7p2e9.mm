include "c7.mm"
include "c2.mm"
include "caddc.mm"
include "co.mm"
include "c8.mm"
include "c1.mm"
include "c9.mm"
include "df-2.mm"
include "oveq2i.mm"
include "7cn.mm"
include "ax-1cn.mm"
include "addassi.mm"
include "eqtr4i.mm"
include "df-8.mm"
include "oveq1i.mm"
include "df-9.mm"

theorem 7p2e9



  assert |- ( 7 + 2 ) = 9

  proof
    c7
    c2
    caddc
    co
    #
    c8
    c1
    caddc
    co
    #
    c9
    @0
    c7
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
    c7
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
    c7
    caddc
    df-2
    oveq2i
    c7
    c1
    c1
    7cn
    ax-1cn
    ax-1cn
    addassi
    eqtr4i
    c8
    @2
    c1
    caddc
    df-8
    oveq1i
    eqtr4i
    df-9
    eqtr4i
end
