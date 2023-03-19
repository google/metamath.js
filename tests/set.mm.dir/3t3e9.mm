include "c3.mm"
include "cmul.mm"
include "co.mm"
include "c2.mm"
include "c1.mm"
include "caddc.mm"
include "c9.mm"
include "df-3.mm"
include "oveq2i.mm"
include "c6.mm"
include "3cn.mm"
include "2cn.mm"
include "ax-1cn.mm"
include "adddii.mm"
include "3t2e6.mm"
include "3t1e3.mm"
include "oveq12i.mm"
include "eqtri.mm"
include "6p3e9.mm"

theorem 3t3e9



  assert |- ( 3 x. 3 ) = 9

  proof
    c3
    c3
    cmul
    co
    c3
    c2
    c1
    caddc
    co
    #
    cmul
    co
    #
    c9
    c3
    @0
    c3
    cmul
    df-3
    oveq2i
    @1
    c6
    c3
    caddc
    co
    #
    c9
    @1
    c3
    c2
    cmul
    co
    #
    c3
    c1
    cmul
    co
    #
    caddc
    co
    @2
    c3
    c2
    c1
    3cn
    2cn
    ax-1cn
    adddii
    @3
    c6
    @4
    c3
    caddc
    3t2e6
    3t1e3
    oveq12i
    eqtri
    6p3e9
    eqtri
    eqtri
end
