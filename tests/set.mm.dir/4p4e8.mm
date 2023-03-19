include "c4.mm"
include "caddc.mm"
include "co.mm"
include "c3.mm"
include "c1.mm"
include "c8.mm"
include "df-4.mm"
include "oveq2i.mm"
include "4cn.mm"
include "3cn.mm"
include "ax-1cn.mm"
include "addassi.mm"
include "eqtr4i.mm"
include "c7.mm"
include "df-8.mm"
include "4p3e7.mm"
include "oveq1i.mm"

theorem 4p4e8



  assert |- ( 4 + 4 ) = 8

  proof
    c4
    c4
    caddc
    co
    #
    c4
    c3
    caddc
    co
    #
    c1
    caddc
    co
    #
    c8
    @0
    c4
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
    c4
    caddc
    df-4
    oveq2i
    c4
    c3
    c1
    4cn
    3cn
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
    4p3e7
    oveq1i
    eqtr4i
    eqtr4i
end
