include "c7.mm"
include "c3.mm"
include "caddc.mm"
include "co.mm"
include "c2.mm"
include "c1.mm"
include "c10.mm"
include "df-3.mm"
include "oveq2i.mm"
include "7cn.mm"
include "2cn.mm"
include "ax-1cn.mm"
include "addassi.mm"
include "eqtr4i.mm"
include "c9.mm"
include "df-10OLD.mm"
include "7p2e9.mm"
include "oveq1i.mm"

theorem 7p3e10OLD



  assert |- ( 7 + 3 ) = 10

  proof
    c7
    c3
    caddc
    co
    #
    c7
    c2
    caddc
    co
    #
    c1
    caddc
    co
    #
    c10
    @0
    c7
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
    c7
    caddc
    df-3
    oveq2i
    c7
    c2
    c1
    7cn
    2cn
    ax-1cn
    addassi
    eqtr4i
    c10
    c9
    c1
    caddc
    co
    @2
    df-10OLD
    @1
    c9
    c1
    caddc
    7p2e9
    oveq1i
    eqtr4i
    eqtr4i
end
