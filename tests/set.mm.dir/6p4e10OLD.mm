include "c6.mm"
include "c4.mm"
include "caddc.mm"
include "co.mm"
include "c3.mm"
include "c1.mm"
include "c10.mm"
include "df-4.mm"
include "oveq2i.mm"
include "6cn.mm"
include "3cn.mm"
include "ax-1cn.mm"
include "addassi.mm"
include "eqtr4i.mm"
include "c9.mm"
include "df-10OLD.mm"
include "6p3e9.mm"
include "oveq1i.mm"

theorem 6p4e10OLD



  assert |- ( 6 + 4 ) = 10

  proof
    c6
    c4
    caddc
    co
    #
    c6
    c3
    caddc
    co
    #
    c1
    caddc
    co
    #
    c10
    @0
    c6
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
    c6
    caddc
    df-4
    oveq2i
    c6
    c3
    c1
    6cn
    3cn
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
    6p3e9
    oveq1i
    eqtr4i
    eqtr4i
end
