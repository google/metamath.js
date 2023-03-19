include "c6.mm"
include "c2.mm"
include "caddc.mm"
include "co.mm"
include "c7.mm"
include "c1.mm"
include "c8.mm"
include "df-2.mm"
include "oveq2i.mm"
include "6cn.mm"
include "ax-1cn.mm"
include "addassi.mm"
include "eqtr4i.mm"
include "df-7.mm"
include "oveq1i.mm"
include "df-8.mm"

theorem 6p2e8



  assert |- ( 6 + 2 ) = 8

  proof
    c6
    c2
    caddc
    co
    #
    c7
    c1
    caddc
    co
    #
    c8
    @0
    c6
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
    c6
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
    c6
    caddc
    df-2
    oveq2i
    c6
    c1
    c1
    6cn
    ax-1cn
    ax-1cn
    addassi
    eqtr4i
    c7
    @2
    c1
    caddc
    df-7
    oveq1i
    eqtr4i
    df-8
    eqtr4i
end
