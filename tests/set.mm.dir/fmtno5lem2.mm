include "c6.mm"
include "c5.mm"
include "cdc.mm"
include "c3.mm"
include "c2.mm"
include "c7.mm"
include "c8.mm"
include "cc0.mm"
include "5nn0.mm"
include "6nn0.mm"
include "deccl.mm"
include "3nn0.mm"
include "eqid.mm"
include "0nn0.mm"
include "cmul.mm"
include "co.mm"
include "2nn0.mm"
include "7nn0.mm"
include "c1.mm"
include "1nn0.mm"
include "5p1e6.mm"
include "6t5e30.mm"
include "2cn.mm"
include "addid2i.mm"
include "decaddi.mm"
include "5t5e25.mm"
include "decmul1c.mm"
include "5p2e7.mm"
include "decsuc.mm"
include "5cn.mm"
include "3cn.mm"
include "5t3e15.mm"
include "mulcomli.mm"
include "5p3e8.mm"

theorem fmtno5lem2
  let vk: setvar k
  let vx: setvar x


  assert |- ( ; ; ; ; 6 5 5 3 6 x. 5 ) = ; ; ; ; ; 3 2 7 6 8 0

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
    c2
    cdc
    #
    c7
    cdc
    #
    c6
    cdc
    #
    c8
    cdc
    cc0
    c5
    c3
    @2
    c6
    cdc
    #
    5nn0
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
    0nn0
    3nn0
    @5
    c5
    c8
    @2
    c5
    cmul
    co
    c3
    @4
    c6
    @3
    c7
    c3
    c2
    3nn0
    2nn0
    deccl
    #
    7nn0
    deccl
    #
    6nn0
    deccl
    5nn0
    3nn0
    @1
    c3
    @5
    c5
    c5
    c1
    @2
    5nn0
    @8
    3nn0
    @2
    eqid
    5nn0
    1nn0
    @4
    c5
    c6
    @1
    c5
    cmul
    co
    @10
    5nn0
    5p1e6
    @0
    c5
    @4
    c5
    c5
    c2
    @1
    5nn0
    @7
    5nn0
    @1
    eqid
    5nn0
    2nn0
    @3
    c5
    c7
    @0
    c5
    cmul
    co
    c2
    @9
    5nn0
    2nn0
    c6
    c5
    @3
    c5
    c5
    c2
    @0
    5nn0
    6nn0
    5nn0
    @0
    eqid
    5nn0
    2nn0
    c3
    cc0
    c2
    c6
    c5
    cmul
    co
    c2
    3nn0
    0nn0
    2nn0
    6t5e30
    c2
    2cn
    addid2i
    decaddi
    5t5e25
    decmul1c
    5p2e7
    decaddi
    5t5e25
    decmul1c
    decsuc
    c5
    c3
    c1
    c5
    cdc
    5cn
    3cn
    5t3e15
    mulcomli
    decmul1c
    5p3e8
    decaddi
    6t5e30
    decmul1c
end
