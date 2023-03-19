include "c5.mm"
include "c4.mm"
include "caddc.mm"
include "co.mm"
include "c3.mm"
include "c1.mm"
include "c9.mm"
include "df-4.mm"
include "oveq2i.mm"
include "5cn.mm"
include "3cn.mm"
include "ax-1cn.mm"
include "addassi.mm"
include "eqtr4i.mm"
include "c8.mm"
include "df-9.mm"
include "5p3e8.mm"
include "oveq1i.mm"

theorem 5p4e9



  assert |- ( 5 + 4 ) = 9

  proof
    c5
    c4
    caddc
    co
    #
    c5
    c3
    caddc
    co
    #
    c1
    caddc
    co
    #
    c9
    @0
    c5
    c3
    c1
    caddc
    co
    #
    caddc
    co
    @2
    c4
    @3
    c5
    caddc
    df-4
    oveq2i
    c5
    c3
    c1
    5cn
    3cn
    ax-1cn
    addassi
    eqtr4i
    c9
    c8
    c1
    caddc
    co
    @2
    df-9
    @1
    c8
    c1
    caddc
    5p3e8
    oveq1i
    eqtr4i
    eqtr4i
end
