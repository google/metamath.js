include "c4.mm"
include "c3.mm"
include "caddc.mm"
include "co.mm"
include "c2.mm"
include "c1.mm"
include "c7.mm"
include "df-3.mm"
include "oveq2i.mm"
include "4cn.mm"
include "2cn.mm"
include "ax-1cn.mm"
include "addassi.mm"
include "eqtr4i.mm"
include "c6.mm"
include "df-7.mm"
include "4p2e6.mm"
include "oveq1i.mm"

theorem 4p3e7



  assert |- ( 4 + 3 ) = 7

  proof
    c4
    c3
    caddc
    co
    #
    c4
    c2
    caddc
    co
    #
    c1
    caddc
    co
    #
    c7
    @0
    c4
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
    c4
    caddc
    df-3
    oveq2i
    c4
    c2
    c1
    4cn
    2cn
    ax-1cn
    addassi
    eqtr4i
    c7
    c6
    c1
    caddc
    co
    @2
    df-7
    @1
    c6
    c1
    caddc
    4p2e6
    oveq1i
    eqtr4i
    eqtr4i
end
