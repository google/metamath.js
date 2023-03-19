include "c2.mm"
include "c1.mm"
include "c6.mm"
include "cdc.mm"
include "cc0.mm"
include "c7.mm"
include "c8.mm"
include "c3.mm"
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
include "6nn0.mm"
include "0z.mm"
include "8nn0.mm"
include "3nn0.mm"
include "cexp.mm"
include "co.mm"
include "nn0zi.mm"
include "nn0expcli.mm"
include "cmo.mm"
include "eqid.mm"
include "nn0cni.mm"
include "2cn.mm"
include "8t2e16.mm"
include "mulcomli.mm"
include "cmul.mm"
include "caddc.mm"
include "c4.mm"
include "9nn0.mm"
include "4nn0.mm"
include "7nn0.mm"
include "0nn0.mm"
include "dec0h.mm"
include "4cn.mm"
include "addid2i.mm"
include "oveq1i.mm"
include "4p1e5.mm"
include "eqtri.mm"
include "7cn.mm"
include "6cn.mm"
include "7p6e13.mm"
include "addcomli.mm"
include "decaddc.mm"
include "2p1e3.mm"
include "5cn.mm"
include "6p5e11.mm"
include "10nn0.mm"
include "3cn.mm"
include "dec10p.mm"
include "mulid1i.mm"
include "1p0e1.mm"
include "oveq12i.mm"
include "5p1e6.mm"
include "3p2e5.mm"
include "3eqtri.mm"
include "decmac.mm"
include "5t2e10.mm"
include "00id.mm"
include "2t2e4.mm"
include "decma2c.mm"
include "5t5e25.mm"
include "decsuc.mm"
include "decaddi.mm"
include "decrmac.mm"
include "9cn.mm"
include "9t5e45.mm"
include "5p2e7.mm"
include "9t2e18.mm"
include "1p1e2.mm"
include "8p8e16.mm"
include "decaddci.mm"
include "2exp16.mm"
include "numexp2x.mm"
include "3eqtr2i.mm"
include "mod2xi.mm"
include "6p1e7.mm"
include "nncni.mm"
include "mul02i.mm"
include "6t2e12.mm"
include "decmul1c.mm"
include "3eqtr4i.mm"
include "modxp1i.mm"

theorem 1259lem1
  let cN: class N
  assume 1259prm.1: |- N = ; ; ; 1 2 5 9


  assert |- ( ( 2 ^ ; 1 7 ) mod N ) = ( ; ; 1 3 6 mod N )

  proof
    c2
    c1
    c6
    cdc
    #
    cc0
    c1
    c7
    cdc
    c6
    c8
    cdc
    #
    c1
    c3
    cdc
    #
    c6
    cdc
    #
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
    @5
    c9
    @4
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
    c1
    c6
    1nn0
    6nn0
    deccl
    0z
    c6
    c8
    6nn0
    8nn0
    deccl
    #
    @2
    c6
    c1
    c3
    1nn0
    3nn0
    deccl
    6nn0
    deccl
    #
    c2
    c8
    c5
    c2
    cdc
    #
    @0
    c2
    c8
    cexp
    co
    #
    @1
    cN
    @8
    2nn
    8nn0
    @11
    c5
    c2
    5nn0
    2nn0
    deccl
    #
    nn0zi
    c2
    c8
    2nn0
    8nn0
    nn0expcli
    @9
    @12
    cN
    cmo
    co
    eqid
    c8
    c2
    @0
    c8
    8nn0
    nn0cni
    2cn
    8t2e16
    mulcomli
    #
    @11
    cN
    cmul
    co
    @1
    caddc
    co
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
    c2
    @0
    cexp
    co
    @12
    @12
    cmul
    co
    #
    @5
    c9
    c6
    c8
    @11
    @17
    c6
    c4
    c7
    cdc
    #
    cN
    @1
    @7
    9nn0
    6nn0
    8nn0
    1259prm.1
    @1
    eqid
    #
    @13
    6nn0
    c4
    c7
    4nn0
    7nn0
    deccl
    @4
    c5
    c5
    c3
    @11
    @16
    c3
    c2
    c6
    cdc
    #
    @5
    c6
    @19
    caddc
    co
    @6
    5nn0
    5nn0
    3nn0
    @5
    eqid
    cc0
    c6
    c4
    c7
    c5
    c3
    c6
    @19
    0nn0
    6nn0
    4nn0
    7nn0
    c6
    6nn0
    dec0h
    @19
    eqid
    cc0
    c4
    caddc
    co
    #
    c1
    caddc
    co
    c4
    c1
    caddc
    co
    #
    c5
    @22
    c4
    c1
    caddc
    c4
    4cn
    addid2i
    oveq1i
    4p1e5
    eqtri
    3nn0
    c7
    c6
    @2
    7cn
    6cn
    7p6e13
    addcomli
    decaddc
    @13
    3nn0
    c2
    c6
    2nn0
    6nn0
    deccl
    c1
    c2
    c3
    c1
    @11
    @15
    c5
    c1
    cc0
    cdc
    #
    @4
    c5
    @21
    caddc
    co
    1nn0
    2nn0
    3nn0
    1nn0
    @4
    eqid
    cc0
    c5
    c2
    c6
    c3
    c1
    c5
    @21
    0nn0
    5nn0
    2nn0
    6nn0
    c5
    5nn0
    dec0h
    #
    @21
    eqid
    cc0
    c2
    caddc
    co
    #
    c1
    caddc
    co
    c2
    c1
    caddc
    co
    c3
    @26
    c2
    c1
    caddc
    c2
    2cn
    addid2i
    oveq1i
    2p1e3
    eqtri
    1nn0
    c6
    c5
    c1
    c1
    cdc
    6cn
    5cn
    6p5e11
    addcomli
    decaddc
    @13
    5nn0
    10nn0
    c5
    c2
    c1
    c3
    c1
    c6
    c5
    cc0
    @11
    c3
    @24
    caddc
    co
    5nn0
    2nn0
    1nn0
    3nn0
    @11
    eqid
    #
    @24
    c3
    @2
    @24
    10nn0
    nn0cni
    3cn
    c3
    dec10p
    addcomli
    1nn0
    5nn0
    0nn0
    c5
    c1
    cmul
    co
    #
    c1
    cc0
    caddc
    co
    #
    caddc
    co
    c5
    c1
    caddc
    co
    c6
    @28
    c5
    @29
    c1
    caddc
    c5
    5cn
    mulid1i
    1p0e1
    oveq12i
    5p1e6
    eqtri
    c2
    c1
    cmul
    co
    #
    c3
    caddc
    co
    c2
    c3
    caddc
    co
    c5
    cc0
    c5
    cdc
    #
    @30
    c2
    c3
    caddc
    c2
    2cn
    mulid1i
    oveq1i
    c3
    c2
    c5
    3cn
    2cn
    3p2e5
    addcomli
    @25
    3eqtri
    decmac
    c5
    c2
    cc0
    c1
    c2
    @24
    c5
    cc0
    @11
    c1
    5nn0
    2nn0
    0nn0
    1nn0
    @27
    c1
    1nn0
    dec0h
    2nn0
    5nn0
    0nn0
    c5
    c2
    cmul
    co
    #
    cc0
    cc0
    caddc
    co
    #
    caddc
    co
    @24
    cc0
    caddc
    co
    @24
    @32
    @24
    @33
    cc0
    caddc
    5t2e10
    00id
    oveq12i
    cc0
    dec10p
    eqtri
    c2
    c2
    cmul
    co
    #
    c1
    caddc
    co
    @23
    c5
    @31
    @34
    c4
    c1
    caddc
    2t2e4
    oveq1i
    4p1e5
    @25
    3eqtri
    decmac
    decma2c
    c5
    c2
    c5
    @21
    c3
    c1
    @11
    c3
    5nn0
    2nn0
    3nn0
    @27
    5nn0
    3nn0
    1nn0
    c2
    c5
    c6
    c5
    c5
    cmul
    co
    2nn0
    5nn0
    5p1e6
    5t5e25
    decsuc
    c1
    cc0
    c3
    c2
    c5
    cmul
    co
    c3
    1nn0
    0nn0
    3nn0
    c5
    c2
    @24
    5cn
    2cn
    5t2e10
    mulcomli
    c3
    3cn
    addid2i
    decaddi
    decrmac
    decma2c
    c5
    c2
    c9
    @19
    c6
    c2
    @11
    c8
    5nn0
    2nn0
    8nn0
    @27
    9nn0
    6nn0
    2nn0
    c4
    c5
    c7
    c5
    c9
    cmul
    co
    c2
    4nn0
    5nn0
    2nn0
    c9
    c5
    c4
    c5
    cdc
    9cn
    5cn
    9t5e45
    mulcomli
    5p2e7
    decaddi
    c1
    c8
    c6
    c2
    c2
    c9
    cmul
    co
    c8
    1nn0
    8nn0
    8nn0
    c9
    c2
    c1
    c8
    cdc
    9cn
    2cn
    9t2e18
    mulcomli
    1p1e2
    6nn0
    8p8e16
    decaddci
    decrmac
    decma2c
    2exp16
    c2
    @18
    @12
    c8
    @0
    2nn0
    8nn0
    @14
    @12
    eqid
    @18
    eqid
    numexp2x
    3eqtr2i
    mod2xi
    c1
    c6
    c7
    @0
    1nn0
    6nn0
    6p1e7
    @0
    eqid
    decsuc
    cc0
    @3
    caddc
    co
    @3
    cc0
    cN
    cmul
    co
    #
    @3
    caddc
    co
    @1
    c2
    cmul
    co
    @3
    @3
    @10
    nn0cni
    addid2i
    @35
    cc0
    @3
    caddc
    cN
    cN
    @8
    nncni
    mul02i
    oveq1i
    c6
    c8
    @2
    c6
    c2
    c1
    @1
    2nn0
    6nn0
    8nn0
    @20
    6nn0
    1nn0
    c1
    c2
    c3
    c6
    c2
    cmul
    co
    1nn0
    2nn0
    2p1e3
    6t2e12
    decsuc
    8t2e16
    decmul1c
    3eqtr4i
    modxp1i
end
