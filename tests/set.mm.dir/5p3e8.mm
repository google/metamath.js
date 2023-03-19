include "c5.mm"
include "c3.mm"
include "caddc.mm"
include "co.mm"
include "c2.mm"
include "c1.mm"
include "c8.mm"
include "df-3.mm"
include "oveq2i.mm"
include "5cn.mm"
include "2cn.mm"
include "ax-1cn.mm"
include "addassi.mm"
include "eqtr4i.mm"
include "c7.mm"
include "df-8.mm"
include "5p2e7.mm"
include "oveq1i.mm"

theorem 5p3e8



  assert |- ( 5 + 3 ) = 8

  proof
    c5
    c3
    caddc
    co
    #
    c5
    c2
    caddc
    co
    #
    c1
    caddc
    co
    #
    c8
    @0
    c5
    c2
    c1
    caddc
    co
    #
    caddc
    co
    @2
    c3
    @3
    c5
    caddc
    df-3
    oveq2i
    c5
    c2
    c1
    5cn
    2cn
    ax-1cn
    addassi
    eqtr4i
    c8
    c7
    c1
    caddc
    co
    @2
    df-8
    @1
    c7
    c1
    caddc
    5p2e7
    oveq1i
    eqtr4i
    eqtr4i
end
