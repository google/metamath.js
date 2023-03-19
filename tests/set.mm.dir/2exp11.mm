include "c2.mm"
include "c1.mm"
include "cdc.mm"
include "cexp.mm"
include "co.mm"
include "c8.mm"
include "c3.mm"
include "cmul.mm"
include "cc0.mm"
include "c4.mm"
include "caddc.mm"
include "8p3e11.mm"
include "eqcomi.mm"
include "oveq2i.mm"
include "cc.mm"
include "wcel.mm"
include "cn0.mm"
include "wceq.mm"
include "2cn.mm"
include "8nn0.mm"
include "3nn0.mm"
include "expadd.mm"
include "mp3an.mm"
include "eqtri.mm"
include "c5.mm"
include "c6.mm"
include "2exp8.mm"
include "cu2.mm"
include "oveq12i.mm"
include "2nn0.mm"
include "5nn0.mm"
include "deccl.mm"
include "6nn0.mm"
include "eqid.mm"
include "4nn0.mm"
include "0nn0.mm"
include "1nn0.mm"
include "8cn.mm"
include "8t2e16.mm"
include "mulcomli.mm"
include "1p1e2.mm"
include "6p4e10.mm"
include "decaddci.mm"
include "5cn.mm"
include "8t5e40.mm"
include "decmul1c.mm"
include "4cn.mm"
include "addid2i.mm"
include "decaddi.mm"
include "6cn.mm"
include "8t6e48.mm"

theorem 2exp11
  let vk: setvar k
  let vx: setvar x


  assert |- ( 2 ^ ; 1 1 ) = ; ; ; 2 0 4 8

  proof
    c2
    c1
    c1
    cdc
    #
    cexp
    co
    #
    c2
    c8
    cexp
    co
    #
    c2
    c3
    cexp
    co
    #
    cmul
    co
    #
    c2
    cc0
    cdc
    #
    c4
    cdc
    #
    c8
    cdc
    #
    @1
    c2
    c8
    c3
    caddc
    co
    #
    cexp
    co
    #
    @4
    @0
    @8
    c2
    cexp
    @8
    @0
    8p3e11
    eqcomi
    oveq2i
    c2
    cc
    wcel
    c8
    cn0
    wcel
    c3
    cn0
    wcel
    @9
    @4
    wceq
    2cn
    8nn0
    3nn0
    c2
    c8
    c3
    expadd
    mp3an
    eqtri
    @4
    c2
    c5
    cdc
    #
    c6
    cdc
    #
    c8
    cmul
    co
    @7
    @2
    @11
    @3
    c8
    cmul
    2exp8
    cu2
    oveq12i
    @10
    c6
    @6
    c8
    c8
    c4
    @11
    8nn0
    c2
    c5
    2nn0
    5nn0
    deccl
    6nn0
    @11
    eqid
    8nn0
    4nn0
    @5
    cc0
    c4
    @10
    c8
    cmul
    co
    c4
    c2
    cc0
    2nn0
    0nn0
    deccl
    0nn0
    4nn0
    c2
    c5
    @5
    cc0
    c8
    c4
    @10
    8nn0
    2nn0
    5nn0
    @10
    eqid
    0nn0
    4nn0
    c1
    c6
    cc0
    c2
    c2
    c8
    cmul
    co
    c4
    1nn0
    6nn0
    4nn0
    c8
    c2
    c1
    c6
    cdc
    8cn
    2cn
    8t2e16
    mulcomli
    1p1e2
    0nn0
    6p4e10
    decaddci
    c8
    c5
    c4
    cc0
    cdc
    8cn
    5cn
    8t5e40
    mulcomli
    decmul1c
    c4
    4cn
    addid2i
    decaddi
    c8
    c6
    c4
    c8
    cdc
    8cn
    6cn
    8t6e48
    mulcomli
    decmul1c
    eqtri
    eqtri
end
