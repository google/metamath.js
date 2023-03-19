include "c6.mm"
include "c3.mm"
include "caddc.mm"
include "co.mm"
include "c2.mm"
include "c1.mm"
include "c9.mm"
include "df-3.mm"
include "oveq2i.mm"
include "6cn.mm"
include "2cn.mm"
include "ax-1cn.mm"
include "addassi.mm"
include "eqtr4i.mm"
include "c8.mm"
include "df-9.mm"
include "6p2e8.mm"
include "oveq1i.mm"

theorem 6p3e9



  assert |- ( 6 + 3 ) = 9

  proof
    c6
    c3
    caddc
    co
    #
    c6
    c2
    caddc
    co
    #
    c1
    caddc
    co
    #
    c9
    @0
    c6
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
    c6
    caddc
    df-3
    oveq2i
    c6
    c2
    c1
    6cn
    2cn
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
    6p2e8
    oveq1i
    eqtr4i
    eqtr4i
end
