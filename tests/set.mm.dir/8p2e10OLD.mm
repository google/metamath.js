include "c8.mm"
include "c2.mm"
include "caddc.mm"
include "co.mm"
include "c9.mm"
include "c1.mm"
include "c10.mm"
include "df-2.mm"
include "oveq2i.mm"
include "8cn.mm"
include "ax-1cn.mm"
include "addassi.mm"
include "eqtr4i.mm"
include "df-9.mm"
include "oveq1i.mm"
include "df-10OLD.mm"

theorem 8p2e10OLD



  assert |- ( 8 + 2 ) = 10

  proof
    c8
    c2
    caddc
    co
    #
    c9
    c1
    caddc
    co
    #
    c10
    @0
    c8
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
    c8
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
    c8
    caddc
    df-2
    oveq2i
    c8
    c1
    c1
    8cn
    ax-1cn
    ax-1cn
    addassi
    eqtr4i
    c9
    @2
    c1
    caddc
    df-9
    oveq1i
    eqtr4i
    df-10OLD
    eqtr4i
end
