include "c4.mm"
include "cc0.mm"
include "cdc.mm"
include "c2.mm"
include "c5.mm"
include "c6.mm"
include "c8.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "c7.mm"
include "c9.mm"
include "cmul.mm"
include "cfmtno.mm"
include "cfv.mm"
include "4nn0.mm"
include "2nn0.mm"
include "deccl.mm"
include "8nn0.mm"
include "6nn0.mm"
include "0nn0.mm"
include "7nn0.mm"
include "1nn0.mm"
include "fmtno5faclem3.mm"
include "deceq1i.mm"
include "eqid.mm"
include "9nn0.mm"
include "6p1e7.mm"
include "8p1e9.mm"
include "decsuc.mm"
include "8p6e14.mm"
include "decaddci.mm"
include "7cn.mm"
include "2cn.mm"
include "7p2e9.mm"
include "addcomli.mm"
include "decadd.mm"
include "6cn.mm"
include "addid1i.mm"
include "8p4e12.mm"
include "decaddc.mm"
include "addid2i.mm"
include "fmtno5faclem2.mm"
include "eqcomi.mm"
include "fmtno5faclem1.mm"
include "decmul10add.mm"
include "nn0cni.mm"
include "mulid1i.mm"
include "fmtno5.mm"
include "3eqtr4ri.mm"

theorem fmtno5fac
  let vk: setvar k
  let vx: setvar x


  assert |- ( FermatNo ` 5 ) = ( ; ; ; ; ; ; 6 7 0 0 4 1 7 x. ; ; 6 4 1 )

  proof
    c4
    cc0
    cdc
    c2
    cdc
    cc0
    cdc
    c2
    cdc
    c5
    cdc
    cc0
    cdc
    c2
    cdc
    #
    cc0
    cdc
    c2
    c6
    cdc
    c8
    cdc
    cc0
    cdc
    c1
    cdc
    c6
    cdc
    c6
    cdc
    c8
    cdc
    #
    caddc
    co
    #
    cc0
    cdc
    #
    c6
    c7
    cdc
    #
    cc0
    cdc
    #
    cc0
    cdc
    #
    c4
    cdc
    #
    c1
    cdc
    #
    c7
    cdc
    #
    caddc
    co
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
    @9
    c6
    c4
    cdc
    #
    c1
    cdc
    cmul
    co
    c5
    cfmtno
    cfv
    @10
    c8
    cdc
    #
    c8
    cdc
    #
    c2
    cdc
    #
    c6
    cdc
    #
    c6
    cdc
    #
    c8
    cdc
    #
    c8
    cdc
    #
    cc0
    @8
    c7
    @17
    c7
    @3
    @9
    @24
    c8
    @23
    c8
    @22
    c6
    @21
    c6
    @20
    c2
    @19
    c8
    @10
    c8
    c4
    c2
    4nn0
    2nn0
    deccl
    #
    8nn0
    deccl
    #
    8nn0
    deccl
    #
    2nn0
    deccl
    #
    6nn0
    deccl
    #
    6nn0
    deccl
    #
    8nn0
    deccl
    #
    8nn0
    deccl
    0nn0
    @7
    c1
    @6
    c4
    @5
    cc0
    @4
    cc0
    c6
    c7
    6nn0
    7nn0
    deccl
    #
    0nn0
    deccl
    #
    0nn0
    deccl
    #
    4nn0
    deccl
    #
    1nn0
    deccl
    #
    7nn0
    @2
    @25
    cc0
    fmtno5faclem3
    deceq1i
    @9
    eqid
    @24
    c8
    @7
    c1
    @16
    c9
    @25
    @8
    @32
    8nn0
    @36
    1nn0
    @25
    eqid
    @8
    eqid
    @23
    c8
    @6
    c4
    @15
    c2
    @24
    @7
    @31
    8nn0
    @35
    4nn0
    @24
    eqid
    @7
    eqid
    @14
    c6
    c7
    @23
    @6
    caddc
    co
    @13
    c6
    @12
    c9
    @11
    c4
    @10
    c9
    @26
    9nn0
    deccl
    4nn0
    deccl
    9nn0
    deccl
    6nn0
    deccl
    6nn0
    6p1e7
    @22
    c6
    @5
    cc0
    @14
    c6
    @23
    @6
    @30
    6nn0
    @34
    0nn0
    @23
    eqid
    @6
    eqid
    @21
    c6
    @4
    cc0
    @13
    c6
    @22
    @5
    @29
    6nn0
    @33
    0nn0
    @22
    eqid
    @5
    eqid
    @20
    c2
    c6
    c7
    @12
    c9
    @21
    @4
    @28
    2nn0
    6nn0
    7nn0
    @21
    eqid
    @4
    eqid
    @19
    c8
    c4
    @11
    @20
    c6
    @27
    8nn0
    6nn0
    @20
    eqid
    @10
    c8
    c9
    @19
    @26
    8nn0
    8p1e9
    @19
    eqid
    decsuc
    4nn0
    8p6e14
    decaddci
    c7
    c2
    c9
    7cn
    2cn
    7p2e9
    addcomli
    decadd
    c6
    6cn
    addid1i
    #
    decadd
    @38
    decadd
    decsuc
    2nn0
    8p4e12
    decaddc
    8p1e9
    decadd
    c7
    7cn
    addid2i
    decadd
    @18
    c1
    @2
    @9
    @9
    c6
    c4
    6nn0
    4nn0
    deccl
    1nn0
    @8
    c7
    @37
    7nn0
    deccl
    #
    @9
    @18
    cmul
    co
    @2
    c6
    c4
    @0
    @1
    @9
    6nn0
    4nn0
    @39
    @9
    c6
    cmul
    co
    @0
    fmtno5faclem2
    eqcomi
    @9
    c4
    cmul
    co
    @1
    fmtno5faclem1
    eqcomi
    decmul10add
    eqcomi
    @9
    c1
    cmul
    co
    @9
    @9
    @9
    @39
    nn0cni
    mulid1i
    eqcomi
    decmul10add
    fmtno5
    3eqtr4ri
end
