include "c2.mm"
include "c1.mm"
include "cdc.mm"
include "cexp.mm"
include "co.mm"
include "cmin.mm"
include "cc0.mm"
include "c4.mm"
include "c7.mm"
include "c8.mm"
include "c9.mm"
include "c3.mm"
include "cmul.mm"
include "c5.mm"
include "2nn0.mm"
include "0nn0.mm"
include "deccl.mm"
include "4nn0.mm"
include "8nn0.mm"
include "1nn0.mm"
include "2exp11.mm"
include "4p1e5.mm"
include "eqid.mm"
include "decsuc.mm"
include "8m1e7.mm"
include "decsubi.mm"
include "3nn0.mm"
include "9nn0.mm"
include "7nn0.mm"
include "caddc.mm"
include "c6.mm"
include "8t2e16.mm"
include "2p2e4.mm"
include "oveq12i.mm"
include "6nn0.mm"
include "1p1e2.mm"
include "6p4e10.mm"
include "decaddci2.mm"
include "eqtri.mm"
include "8t3e24.mm"
include "oveq1i.mm"
include "nn0cni.mm"
include "addid1i.mm"
include "decma2c.mm"
include "9t2e18.mm"
include "8p2e10.mm"
include "9t3e27.mm"
include "decmul2c.mm"
include "decmul1c.mm"
include "eqtr4i.mm"

theorem m11nprm
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( 2 ^ ; 1 1 ) - 1 ) = ( ; 8 9 x. ; 2 3 )

  proof
    c2
    c1
    c1
    cdc
    cexp
    co
    #
    c1
    cmin
    co
    c2
    cc0
    cdc
    #
    c4
    cdc
    #
    c7
    cdc
    c8
    c9
    cdc
    #
    c2
    c3
    cdc
    #
    cmul
    co
    @2
    c8
    c7
    @1
    c5
    cdc
    @0
    c1
    @1
    c4
    c2
    cc0
    2nn0
    0nn0
    deccl
    #
    4nn0
    deccl
    8nn0
    1nn0
    2exp11
    @1
    c4
    c5
    @2
    @5
    4nn0
    4p1e5
    @2
    eqid
    decsuc
    8m1e7
    decsubi
    c8
    c9
    @2
    c7
    @4
    @1
    @3
    c2
    c3
    2nn0
    3nn0
    deccl
    8nn0
    9nn0
    @3
    eqid
    7nn0
    @5
    c2
    c3
    c2
    cc0
    c8
    @1
    c4
    c2
    @4
    @1
    2nn0
    3nn0
    2nn0
    0nn0
    @4
    eqid
    #
    @1
    eqid
    8nn0
    4nn0
    2nn0
    c8
    c2
    cmul
    co
    #
    c2
    c2
    caddc
    co
    #
    caddc
    co
    c1
    c6
    cdc
    #
    c4
    caddc
    co
    @1
    @7
    @9
    @8
    c4
    caddc
    8t2e16
    2p2e4
    oveq12i
    c1
    c6
    c2
    @9
    c4
    1nn0
    6nn0
    4nn0
    @9
    eqid
    1p1e2
    6p4e10
    decaddci2
    eqtri
    c8
    c3
    cmul
    co
    #
    cc0
    caddc
    co
    c2
    c4
    cdc
    #
    cc0
    caddc
    co
    @11
    @10
    @11
    cc0
    caddc
    8t3e24
    oveq1i
    @11
    @11
    c2
    c4
    2nn0
    4nn0
    deccl
    nn0cni
    addid1i
    eqtri
    decma2c
    c2
    c3
    @1
    c7
    c9
    c2
    @4
    9nn0
    2nn0
    3nn0
    @6
    7nn0
    2nn0
    c1
    c8
    c2
    c9
    c2
    cmul
    co
    c2
    1nn0
    8nn0
    2nn0
    9t2e18
    1p1e2
    8p2e10
    decaddci2
    9t3e27
    decmul2c
    decmul1c
    eqtr4i
end
