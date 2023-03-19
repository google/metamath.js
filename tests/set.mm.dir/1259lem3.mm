include "c2.mm"
include "c3.mm"
include "c8.mm"
include "cdc.mm"
include "c4.mm"
include "c7.mm"
include "c6.mm"
include "c1.mm"
include "c5.mm"
include "c9.mm"
include "cn.mm"
include "1nn0.mm"
include "2nn0.mm"
include "deccl.mm"
include "5nn0.mm"
include "9nn.mm"
include "decnncl.mm"
include "eqeltri.mm"
include "2nn.mm"
include "3nn0.mm"
include "8nn0.mm"
include "4z.mm"
include "7nn0.mm"
include "cc0.mm"
include "4nn0.mm"
include "nn0zi.mm"
include "0nn0.mm"
include "6nn0.mm"
include "1259lem2.mm"
include "cexp.mm"
include "co.mm"
include "cmo.mm"
include "2exp4.mm"
include "oveq1i.mm"
include "eqid.mm"
include "4p4e8.mm"
include "decaddi.mm"
include "cmul.mm"
include "caddc.mm"
include "9nn0.mm"
include "10nn0.mm"
include "nn0cni.mm"
include "7cn.mm"
include "dec10p.mm"
include "addcomli.mm"
include "mulid2i.mm"
include "dec0h.mm"
include "0p1e1.mm"
include "3cn.mm"
include "ax-1cn.mm"
include "3p1e4.mm"
include "decadd.mm"
include "2p1e3.mm"
include "decsuc.mm"
include "5p4e9.mm"
include "5cn.mm"
include "7p5e12.mm"
include "decaddci.mm"
include "decmac.mm"
include "9p1e10.mm"
include "9cn.mm"
include "9t11e99.mm"
include "mulcomli.mm"
include "decsucc.mm"
include "decma2c.mm"
include "addid1i.mm"
include "8cn.mm"
include "mulid1i.mm"
include "oveq12i.mm"
include "8p5e13.mm"
include "eqtri.mm"
include "7p2e9.mm"
include "3eqtri.mm"
include "mul02i.mm"
include "2cn.mm"
include "addid2i.mm"
include "8t6e48.mm"
include "4p1e5.mm"
include "8p4e12.mm"
include "7t6e42.mm"
include "decmul1c.mm"
include "6cn.mm"
include "decmul1.mm"
include "decmul2c.mm"
include "eqtr4i.mm"
include "modxai.mm"
include "3t2e6.mm"
include "6p1e7.mm"
include "8t2e16.mm"
include "4cn.mm"
include "4t2e8.mm"
include "8p2e10.mm"
include "5t4e20.mm"
include "9t4e36.mm"
include "6p5e11.mm"
include "7t7e49.mm"
include "7p7e14.mm"
include "decrmac.mm"
include "mod2xi.mm"

theorem 1259lem3
  let cN: class N
  assume 1259prm.1: |- N = ; ; ; 1 2 5 9


  assert |- ( ( 2 ^ ; 7 6 ) mod N ) = ( 5 mod N )

  proof
    c2
    c3
    c8
    cdc
    #
    c4
    c7
    c6
    cdc
    c7
    c1
    cdc
    #
    c5
    cN
    cN
    c1
    c2
    cdc
    #
    c5
    cdc
    #
    c9
    cdc
    cn
    1259prm.1
    @3
    c9
    @2
    c5
    c1
    c2
    1nn0
    2nn0
    deccl
    #
    5nn0
    deccl
    #
    9nn
    decnncl
    eqeltri
    #
    2nn
    c3
    c8
    3nn0
    8nn0
    deccl
    4z
    c7
    c1
    7nn0
    1nn0
    deccl
    #
    5nn0
    c2
    c3
    c4
    cdc
    #
    c4
    c1
    c1
    cdc
    #
    @0
    c8
    c7
    cdc
    #
    cc0
    cdc
    #
    c1
    c6
    cdc
    #
    @1
    cN
    @6
    2nn
    c3
    c4
    3nn0
    4nn0
    deccl
    @9
    c1
    c1
    1nn0
    1nn0
    deccl
    #
    nn0zi
    @10
    cc0
    c8
    c7
    8nn0
    7nn0
    deccl
    #
    0nn0
    deccl
    #
    @7
    4nn0
    c1
    c6
    1nn0
    6nn0
    deccl
    cN
    1259prm.1
    1259lem2
    c2
    c4
    cexp
    co
    @12
    cN
    cmo
    2exp4
    oveq1i
    c3
    c4
    c8
    @8
    c4
    3nn0
    4nn0
    4nn0
    @8
    eqid
    4p4e8
    decaddi
    @9
    cN
    cmul
    co
    @1
    caddc
    co
    c1
    c3
    cdc
    #
    c9
    cdc
    #
    c2
    cdc
    #
    cc0
    cdc
    @11
    @12
    cmul
    co
    @3
    c9
    c7
    c1
    @9
    @18
    cc0
    c1
    cc0
    cdc
    #
    cN
    @1
    @5
    9nn0
    7nn0
    1nn0
    1259prm.1
    @1
    eqid
    #
    @13
    0nn0
    10nn0
    c1
    c1
    c1
    c7
    @3
    @17
    c2
    @16
    @9
    c7
    @19
    caddc
    co
    1nn0
    1nn0
    1nn0
    7nn0
    @9
    eqid
    @19
    c7
    c1
    c7
    cdc
    @19
    10nn0
    nn0cni
    7cn
    c7
    dec10p
    addcomli
    @5
    2nn0
    c1
    c3
    1nn0
    3nn0
    deccl
    @2
    c5
    c1
    c4
    @16
    c9
    c1
    @3
    cmul
    co
    #
    c1
    @16
    caddc
    co
    @4
    5nn0
    1nn0
    4nn0
    @3
    @3
    @5
    nn0cni
    mulid2i
    #
    cc0
    c1
    c1
    c3
    c1
    c4
    c1
    @16
    0nn0
    1nn0
    1nn0
    3nn0
    c1
    1nn0
    dec0h
    @16
    eqid
    0p1e1
    c3
    c1
    c4
    3cn
    ax-1cn
    3p1e4
    addcomli
    decadd
    c1
    c2
    c3
    @2
    1nn0
    2nn0
    2p1e3
    @2
    eqid
    #
    decsuc
    #
    5p4e9
    decadd
    @2
    c5
    c2
    @16
    @21
    c7
    @4
    5nn0
    7nn0
    @22
    @24
    2nn0
    c7
    c5
    @2
    7cn
    5cn
    7p5e12
    addcomli
    decaddci
    decmac
    c9
    @19
    @9
    c9
    cmul
    co
    9nn0
    9p1e10
    c9
    @9
    c9
    c9
    cdc
    9cn
    @9
    @13
    nn0cni
    9t11e99
    mulcomli
    decsucc
    decma2c
    c1
    c6
    @18
    cc0
    @11
    c5
    c2
    cdc
    #
    c2
    cdc
    #
    @12
    @15
    1nn0
    6nn0
    @12
    eqid
    0nn0
    @25
    c2
    c5
    c2
    5nn0
    2nn0
    deccl
    #
    2nn0
    deccl
    @10
    cc0
    @25
    c2
    c1
    @17
    c2
    cc0
    @11
    @26
    @14
    0nn0
    @27
    2nn0
    @11
    eqid
    #
    @26
    eqid
    1nn0
    2nn0
    0nn0
    c8
    c7
    c5
    c2
    c1
    @16
    c9
    cc0
    @10
    @25
    cc0
    caddc
    co
    8nn0
    7nn0
    5nn0
    2nn0
    @10
    eqid
    #
    @25
    @25
    @27
    nn0cni
    addid1i
    1nn0
    9nn0
    0nn0
    c8
    c1
    cmul
    co
    #
    c5
    cc0
    caddc
    co
    #
    caddc
    co
    c8
    c5
    caddc
    co
    @16
    @30
    c8
    @31
    c5
    caddc
    c8
    8cn
    mulid1i
    c5
    5cn
    addid1i
    oveq12i
    8p5e13
    eqtri
    c7
    c1
    cmul
    co
    #
    c2
    caddc
    co
    c7
    c2
    caddc
    co
    c9
    cc0
    c9
    cdc
    @32
    c7
    c2
    caddc
    c7
    7cn
    mulid1i
    oveq1i
    7p2e9
    c9
    9nn0
    dec0h
    3eqtri
    decmac
    cc0
    c1
    cmul
    co
    #
    c2
    caddc
    co
    cc0
    c2
    caddc
    co
    #
    c2
    cc0
    c2
    cdc
    #
    @33
    cc0
    c2
    caddc
    c1
    ax-1cn
    mul02i
    oveq1i
    c2
    2cn
    addid2i
    #
    c2
    2nn0
    dec0h
    #
    3eqtri
    decmac
    @10
    cc0
    @26
    cc0
    c6
    @11
    6nn0
    @14
    0nn0
    @28
    0nn0
    c8
    c7
    @25
    c2
    c6
    c4
    @10
    6nn0
    8nn0
    7nn0
    @29
    2nn0
    4nn0
    c4
    c8
    c2
    c5
    c8
    c6
    cmul
    co
    c4
    4nn0
    8nn0
    4nn0
    8t6e48
    4p1e5
    2nn0
    8p4e12
    decaddci
    7t6e42
    decmul1c
    c6
    6cn
    mul02i
    decmul1
    decmul2c
    eqtr4i
    modxai
    c3
    c8
    c7
    c6
    c2
    c1
    @0
    2nn0
    3nn0
    8nn0
    @0
    eqid
    6nn0
    1nn0
    c2
    c3
    cmul
    co
    #
    c1
    caddc
    co
    c6
    c1
    caddc
    co
    c7
    @38
    c6
    c1
    caddc
    c3
    c2
    c6
    3cn
    2cn
    3t2e6
    mulcomli
    oveq1i
    6p1e7
    eqtri
    c8
    c2
    @12
    8cn
    2cn
    8t2e16
    mulcomli
    decmul2c
    c4
    cN
    cmul
    co
    c5
    caddc
    co
    c5
    cc0
    cdc
    #
    c4
    cdc
    #
    c1
    cdc
    @1
    @1
    cmul
    co
    @3
    c9
    cc0
    c5
    c4
    @40
    c1
    c4
    cN
    c5
    @5
    9nn0
    0nn0
    5nn0
    1259prm.1
    c5
    5nn0
    dec0h
    4nn0
    1nn0
    4nn0
    @2
    c5
    cc0
    c4
    c4
    @39
    c4
    c2
    @3
    cc0
    c4
    caddc
    co
    #
    @4
    5nn0
    0nn0
    4nn0
    @3
    eqid
    @41
    c4
    cc0
    c4
    cdc
    c4
    4cn
    addid2i
    #
    c4
    4nn0
    dec0h
    eqtri
    4nn0
    4nn0
    2nn0
    c1
    c2
    cc0
    c2
    c4
    c5
    cc0
    c1
    @2
    @34
    1nn0
    2nn0
    0nn0
    2nn0
    @23
    @34
    c2
    @35
    @36
    @37
    eqtri
    4nn0
    0nn0
    1nn0
    c4
    c1
    cmul
    co
    #
    cc0
    c1
    caddc
    co
    #
    caddc
    co
    c4
    c1
    caddc
    co
    c5
    @43
    c4
    @44
    c1
    caddc
    c4
    4cn
    mulid1i
    0p1e1
    oveq12i
    4p1e5
    eqtri
    c4
    c2
    cmul
    co
    #
    c2
    caddc
    co
    c8
    c2
    caddc
    co
    @19
    @45
    c8
    c2
    caddc
    4t2e8
    oveq1i
    8p2e10
    eqtri
    decma2c
    c2
    cc0
    c4
    c4
    c5
    cmul
    co
    c4
    2nn0
    0nn0
    4nn0
    c5
    c4
    c2
    cc0
    cdc
    5cn
    4cn
    5t4e20
    mulcomli
    @42
    decaddi
    decma2c
    c3
    c6
    c1
    c4
    c4
    c9
    cmul
    co
    c5
    3nn0
    6nn0
    5nn0
    c9
    c4
    c3
    c6
    cdc
    9cn
    4cn
    9t4e36
    mulcomli
    3p1e4
    1nn0
    6p5e11
    decaddci
    decma2c
    c7
    c1
    @40
    c1
    @1
    c7
    @1
    @7
    7nn0
    1nn0
    @20
    1nn0
    7nn0
    c7
    c1
    c7
    @39
    c4
    c1
    @1
    c7
    7nn0
    1nn0
    7nn0
    @20
    7nn0
    4nn0
    1nn0
    c4
    c5
    c7
    c7
    cmul
    co
    4nn0
    4p1e5
    7t7e49
    decsucc
    c1
    c7
    cmul
    co
    #
    c7
    caddc
    co
    c7
    c7
    caddc
    co
    c1
    c4
    cdc
    @46
    c7
    c7
    caddc
    c7
    7cn
    mulid2i
    oveq1i
    7p7e14
    eqtri
    decrmac
    @1
    @1
    @7
    nn0cni
    mulid1i
    decmul2c
    eqtr4i
    mod2xi
end
