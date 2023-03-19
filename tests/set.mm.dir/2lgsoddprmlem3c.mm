include "c5.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "c1.mm"
include "cmin.mm"
include "c8.mm"
include "cdiv.mm"
include "c3.mm"
include "cmul.mm"
include "c4.mm"
include "caddc.mm"
include "df-5.mm"
include "oveq1i.mm"
include "cc.mm"
include "wcel.mm"
include "wceq.mm"
include "4cn.mm"
include "binom21.mm"
include "ax-mp.mm"
include "eqtri.mm"
include "3cn.mm"
include "8cn.mm"
include "mulcli.mm"
include "ax-1cn.mm"
include "sq4e2t8.mm"
include "2cn.mm"
include "4t2e8.mm"
include "mulid2i.mm"
include "eqtr4i.mm"
include "mulcomli.mm"
include "oveq12i.mm"
include "adddiri.mm"
include "2p1e3.mm"
include "3eqtr2i.mm"
include "mvrraddi.mm"
include "cc0.mm"
include "0re.mm"
include "8pos.mm"
include "gtneii.mm"
include "divcan4i.mm"

theorem 2lgsoddprmlem3c



  assert |- ( ( ( 5 ^ 2 ) - 1 ) / 8 ) = 3

  proof
    c5
    c2
    cexp
    co
    #
    c1
    cmin
    co
    #
    c8
    cdiv
    co
    c3
    c8
    cmul
    co
    #
    c8
    cdiv
    co
    c3
    @1
    @2
    c8
    cdiv
    @1
    c4
    c2
    cexp
    co
    #
    c2
    c4
    cmul
    co
    #
    caddc
    co
    #
    c1
    caddc
    co
    #
    c1
    cmin
    co
    @2
    @0
    @6
    c1
    cmin
    @0
    c4
    c1
    caddc
    co
    #
    c2
    cexp
    co
    #
    @6
    c5
    @7
    c2
    cexp
    df-5
    oveq1i
    c4
    cc
    wcel
    @8
    @6
    wceq
    4cn
    c4
    binom21
    ax-mp
    eqtri
    oveq1i
    @6
    @2
    c1
    c3
    c8
    3cn
    8cn
    mulcli
    ax-1cn
    @5
    @2
    c1
    caddc
    @5
    c2
    c8
    cmul
    co
    #
    c1
    c8
    cmul
    co
    #
    caddc
    co
    c2
    c1
    caddc
    co
    #
    c8
    cmul
    co
    @2
    @3
    @9
    @4
    @10
    caddc
    sq4e2t8
    c4
    c2
    @10
    4cn
    2cn
    c4
    c2
    cmul
    co
    c8
    @10
    4t2e8
    c8
    8cn
    mulid2i
    eqtr4i
    mulcomli
    oveq12i
    c2
    c1
    c8
    2cn
    ax-1cn
    8cn
    adddiri
    @11
    c3
    c8
    cmul
    2p1e3
    oveq1i
    3eqtr2i
    oveq1i
    mvrraddi
    eqtri
    oveq1i
    c3
    c8
    3cn
    8cn
    cc0
    c8
    0re
    8pos
    gtneii
    divcan4i
    eqtri
end
