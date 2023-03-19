include "c6.mm"
include "c5.mm"
include "cdc.mm"
include "c3.mm"
include "c9.mm"
include "c2.mm"
include "c1.mm"
include "6nn0.mm"
include "5nn0.mm"
include "deccl.mm"
include "3nn0.mm"
include "eqid.mm"
include "c8.mm"
include "cmul.mm"
include "co.mm"
include "9nn0.mm"
include "1nn0.mm"
include "8nn0.mm"
include "cc0.mm"
include "0nn0.mm"
include "0p1e1.mm"
include "6t6e36.mm"
include "6p3e9.mm"
include "decaddi.mm"
include "6cn.mm"
include "5cn.mm"
include "6t5e30.mm"
include "mulcomli.mm"
include "decmul1c.mm"
include "3cn.mm"
include "addid2i.mm"
include "decsuc.mm"
include "6t3e18.mm"
include "1p1e2.mm"
include "8p3e11.mm"
include "decaddci.mm"

theorem fmtno5lem1
  let vk: setvar k
  let vx: setvar x


  assert |- ( ; ; ; ; 6 5 5 3 6 x. 6 ) = ; ; ; ; ; 3 9 3 2 1 6

  proof
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
    c3
    c9
    cdc
    #
    c3
    cdc
    #
    c2
    cdc
    #
    c1
    cdc
    c6
    c6
    c3
    @2
    c6
    cdc
    #
    6nn0
    @1
    c3
    @0
    c5
    c6
    c5
    6nn0
    5nn0
    deccl
    #
    5nn0
    deccl
    #
    3nn0
    deccl
    6nn0
    @6
    eqid
    6nn0
    3nn0
    @4
    c1
    cdc
    #
    c8
    c1
    @5
    @2
    c6
    cmul
    co
    c3
    @4
    c1
    @3
    c3
    c3
    c9
    3nn0
    9nn0
    deccl
    #
    3nn0
    deccl
    #
    1nn0
    deccl
    8nn0
    3nn0
    @1
    c3
    @9
    c8
    c6
    c1
    @2
    6nn0
    @8
    3nn0
    @2
    eqid
    8nn0
    1nn0
    @4
    cc0
    c1
    @1
    c6
    cmul
    co
    @11
    0nn0
    0p1e1
    @0
    c5
    @4
    cc0
    c6
    c3
    @1
    6nn0
    @7
    5nn0
    @1
    eqid
    0nn0
    3nn0
    @3
    cc0
    c3
    @0
    c6
    cmul
    co
    c3
    @10
    0nn0
    3nn0
    c6
    c5
    @3
    cc0
    c6
    c3
    @0
    6nn0
    6nn0
    5nn0
    @0
    eqid
    0nn0
    3nn0
    c3
    c6
    c9
    c6
    c6
    cmul
    co
    c3
    3nn0
    6nn0
    3nn0
    6t6e36
    6p3e9
    decaddi
    c6
    c5
    c3
    cc0
    cdc
    6cn
    5cn
    6t5e30
    mulcomli
    #
    decmul1c
    c3
    3cn
    addid2i
    decaddi
    @12
    decmul1c
    decsuc
    c6
    c3
    c1
    c8
    cdc
    6cn
    3cn
    6t3e18
    mulcomli
    decmul1c
    @4
    c1
    c2
    @9
    @11
    1nn0
    1p1e2
    @9
    eqid
    decsuc
    1nn0
    8p3e11
    decaddci
    6t6e36
    decmul1c
end
