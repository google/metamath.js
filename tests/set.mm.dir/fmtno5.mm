include "c5.mm"
include "cfmtno.mm"
include "cfv.mm"
include "c4.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "c2.mm"
include "cexp.mm"
include "caddc.mm"
include "cdc.mm"
include "c9.mm"
include "c6.mm"
include "c7.mm"
include "df-5.mm"
include "fveq2i.mm"
include "cn0.mm"
include "wcel.mm"
include "wceq.mm"
include "4nn0.mm"
include "fmtnorec1.mm"
include "ax-mp.mm"
include "eqtri.mm"
include "2nn0.mm"
include "deccl.mm"
include "9nn0.mm"
include "6nn0.mm"
include "7nn0.mm"
include "6p1e7.mm"
include "c3.mm"
include "5nn0.mm"
include "3nn0.mm"
include "1nn0.mm"
include "fmtno4.mm"
include "3p1e4.mm"
include "eqid.mm"
include "decsuc.mm"
include "6cn.mm"
include "ax-1cn.mm"
include "df-7.mm"
include "mvrraddi.mm"
include "decsubi.mm"
include "oveq1i.mm"
include "fmtno5lem4.mm"

theorem fmtno5
  let vk: setvar k
  let vx: setvar x


  assert |- ( FermatNo ` 5 ) = ; ; ; ; ; ; ; ; ; 4 2 9 4 9 6 7 2 9 7

  proof
    c5
    cfmtno
    cfv
    #
    c4
    cfmtno
    cfv
    #
    c1
    cmin
    co
    #
    c2
    cexp
    co
    #
    c1
    caddc
    co
    #
    c4
    c2
    cdc
    #
    c9
    cdc
    #
    c4
    cdc
    #
    c9
    cdc
    #
    c6
    cdc
    #
    c7
    cdc
    #
    c2
    cdc
    #
    c9
    cdc
    #
    c7
    cdc
    @0
    c4
    c1
    caddc
    co
    #
    cfmtno
    cfv
    #
    @4
    c5
    @13
    cfmtno
    df-5
    fveq2i
    c4
    cn0
    wcel
    @14
    @4
    wceq
    4nn0
    c4
    fmtnorec1
    ax-mp
    eqtri
    @12
    c6
    c7
    @3
    @11
    c9
    @10
    c2
    @9
    c7
    @8
    c6
    @7
    c9
    @6
    c4
    @5
    c9
    c4
    c2
    4nn0
    2nn0
    deccl
    9nn0
    deccl
    4nn0
    deccl
    9nn0
    deccl
    6nn0
    deccl
    7nn0
    deccl
    2nn0
    deccl
    9nn0
    deccl
    6nn0
    6p1e7
    @3
    c6
    c5
    cdc
    #
    c5
    cdc
    #
    c3
    cdc
    #
    c6
    cdc
    #
    c2
    cexp
    co
    @12
    c6
    cdc
    @2
    @18
    c2
    cexp
    @17
    c7
    c6
    @16
    c4
    cdc
    @1
    c1
    @16
    c3
    @15
    c5
    c6
    c5
    6nn0
    5nn0
    deccl
    5nn0
    deccl
    #
    3nn0
    deccl
    7nn0
    1nn0
    fmtno4
    @16
    c3
    c4
    @17
    @19
    3nn0
    3p1e4
    @17
    eqid
    decsuc
    c7
    c6
    c1
    6cn
    ax-1cn
    df-7
    mvrraddi
    decsubi
    oveq1i
    fmtno5lem4
    eqtri
    decsuc
    eqtri
end
