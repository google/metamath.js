include "c5.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "cdc.mm"
include "wceq.mm"
include "c3.mm"
include "cneg.mm"
include "c1.mm"
include "c9.mm"
include "cdiv.mm"
include "c4.mm"
include "caddc.mm"
include "df-5.mm"
include "oveq1i.mm"
include "cmul.mm"
include "cc.mm"
include "wcel.mm"
include "4cn.mm"
include "binom21.mm"
include "ax-mp.mm"
include "c6.mm"
include "c8.mm"
include "sq4e2t8.mm"
include "2cn.mm"
include "8cn.mm"
include "mulcomi.mm"
include "8t2e16.mm"
include "eqtri.mm"
include "4t2e8.mm"
include "oveq12i.mm"
include "1nn0.mm"
include "6nn0.mm"
include "8nn0.mm"
include "eqid.mm"
include "1p1e2.mm"
include "4nn0.mm"
include "6cn.mm"
include "addcomi.mm"
include "8p6e14.mm"
include "decaddci.mm"
include "2nn0.mm"
include "4p1e5.mm"
include "decaddi.mm"
include "cn0.mm"
include "wa.mm"
include "3cn.mm"
include "negcl.mm"
include "pm3.2i.mm"
include "expneg.mm"
include "sqneg.mm"
include "sq3.mm"
include "oveq2i.mm"

theorem ex-exp



  assert |- ( ( 5 ^ 2 ) = ; 2 5 /\ ( -u 3 ^ -u 2 ) = ( 1 / 9 ) )

  proof
    c5
    c2
    cexp
    co
    #
    c2
    c5
    cdc
    #
    wceq
    c3
    cneg
    #
    c2
    cneg
    cexp
    co
    #
    c1
    c9
    cdiv
    co
    #
    wceq
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
    @1
    c5
    @5
    c2
    cexp
    df-5
    oveq1i
    @6
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
    @1
    c4
    cc
    wcel
    @6
    @10
    wceq
    4cn
    c4
    binom21
    ax-mp
    @10
    c2
    c4
    cdc
    #
    c1
    caddc
    co
    @1
    @9
    @11
    c1
    caddc
    @9
    c1
    c6
    cdc
    #
    c8
    caddc
    co
    @11
    @7
    @12
    @8
    c8
    caddc
    @7
    c2
    c8
    cmul
    co
    #
    @12
    sq4e2t8
    @13
    c8
    c2
    cmul
    co
    @12
    c2
    c8
    2cn
    8cn
    mulcomi
    8t2e16
    eqtri
    eqtri
    @8
    c4
    c2
    cmul
    co
    c8
    c2
    c4
    2cn
    4cn
    mulcomi
    4t2e8
    eqtri
    oveq12i
    c1
    c6
    c4
    c2
    @12
    c8
    1nn0
    6nn0
    8nn0
    @12
    eqid
    1p1e2
    4nn0
    c6
    c8
    caddc
    co
    c8
    c6
    caddc
    co
    c1
    c4
    cdc
    c6
    c8
    6cn
    8cn
    addcomi
    8p6e14
    eqtri
    decaddci
    eqtri
    oveq1i
    c2
    c4
    c5
    @11
    c1
    2nn0
    4nn0
    1nn0
    @11
    eqid
    4p1e5
    decaddi
    eqtri
    eqtri
    eqtri
    @3
    c1
    @2
    c2
    cexp
    co
    #
    cdiv
    co
    #
    @4
    @2
    cc
    wcel
    #
    c2
    cn0
    wcel
    #
    wa
    @3
    @15
    wceq
    @16
    @17
    c3
    cc
    wcel
    #
    @16
    3cn
    c3
    negcl
    ax-mp
    2nn0
    pm3.2i
    @2
    c2
    expneg
    ax-mp
    @14
    c9
    c1
    cdiv
    @14
    c3
    c2
    cexp
    co
    #
    c9
    @18
    @14
    @19
    wceq
    3cn
    c3
    sqneg
    ax-mp
    sq3
    eqtri
    oveq2i
    eqtri
    pm3.2i
end
