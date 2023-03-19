include "c3.mm"
include "caddc.mm"
include "co.mm"
include "c2.mm"
include "c1.mm"
include "c6.mm"
include "df-3.mm"
include "oveq2i.mm"
include "3cn.mm"
include "2cn.mm"
include "ax-1cn.mm"
include "addassi.mm"
include "eqtr4i.mm"
include "c5.mm"
include "df-6.mm"
include "3p2e5.mm"
include "oveq1i.mm"

theorem 3p3e6



  assert |- ( 3 + 3 ) = 6

  proof
    c3
    c3
    caddc
    co
    #
    c3
    c2
    caddc
    co
    #
    c1
    caddc
    co
    #
    c6
    @0
    c3
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
    c3
    caddc
    df-3
    oveq2i
    c3
    c2
    c1
    3cn
    2cn
    ax-1cn
    addassi
    eqtr4i
    c6
    c5
    c1
    caddc
    co
    @2
    df-6
    @1
    c5
    c1
    caddc
    3p2e5
    oveq1i
    eqtr4i
    eqtr4i
end
