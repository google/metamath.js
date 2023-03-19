include "c4.mm"
include "c2.mm"
include "caddc.mm"
include "co.mm"
include "c5.mm"
include "c1.mm"
include "c6.mm"
include "df-2.mm"
include "oveq2i.mm"
include "4cn.mm"
include "ax-1cn.mm"
include "addassi.mm"
include "eqtr4i.mm"
include "df-5.mm"
include "oveq1i.mm"
include "df-6.mm"

theorem 4p2e6



  assert |- ( 4 + 2 ) = 6

  proof
    c4
    c2
    caddc
    co
    #
    c5
    c1
    caddc
    co
    #
    c6
    @0
    c4
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
    c4
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
    c4
    caddc
    df-2
    oveq2i
    c4
    c1
    c1
    4cn
    ax-1cn
    ax-1cn
    addassi
    eqtr4i
    c5
    @2
    c1
    caddc
    df-5
    oveq1i
    eqtr4i
    df-6
    eqtr4i
end
