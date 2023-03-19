include "c5.mm"
include "caddc.mm"
include "co.mm"
include "c4.mm"
include "c1.mm"
include "c10.mm"
include "df-5.mm"
include "oveq2i.mm"
include "5cn.mm"
include "4cn.mm"
include "ax-1cn.mm"
include "addassi.mm"
include "eqtr4i.mm"
include "c9.mm"
include "df-10OLD.mm"
include "5p4e9.mm"
include "oveq1i.mm"

theorem 5p5e10OLD



  assert |- ( 5 + 5 ) = 10

  proof
    c5
    c5
    caddc
    co
    #
    c5
    c4
    caddc
    co
    #
    c1
    caddc
    co
    #
    c10
    @0
    c5
    c4
    c1
    caddc
    co
    #
    caddc
    co
    @2
    c5
    @3
    c5
    caddc
    df-5
    oveq2i
    c5
    c4
    c1
    5cn
    4cn
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
    5p4e9
    oveq1i
    eqtr4i
    eqtr4i
end
