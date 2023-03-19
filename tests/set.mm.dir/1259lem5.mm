include "c8.mm"
include "c6.mm"
include "cdc.mm"
include "c9.mm"
include "c1.mm"
include "c2.mm"
include "c3.mm"
include "c4.mm"
include "cexp.mm"
include "co.mm"
include "cmin.mm"
include "cn.mm"
include "wcel.mm"
include "cn0.mm"
include "2nn.mm"
include "3nn0.mm"
include "4nn0.mm"
include "deccl.mm"
include "nnexpcl.mm"
include "mp2an.mm"
include "nnm1nn0.mm"
include "ax-mp.mm"
include "8nn0.mm"
include "6nn0.mm"
include "9nn0.mm"
include "c5.mm"
include "1nn0.mm"
include "2nn0.mm"
include "5nn0.mm"
include "9nn.mm"
include "decnncl.mm"
include "eqeltri.mm"
include "c7.mm"
include "cc0.mm"
include "1259lem2.mm"
include "6p1e7.mm"
include "eqid.mm"
include "decsuc.mm"
include "decsucc.mm"
include "modsubi.mm"
include "0nn0.mm"
include "cgcd.mm"
include "cz.mm"
include "wceq.mm"
include "nn0zi.mm"
include "gcdcom.mm"
include "cdvds.mm"
include "wbr.mm"
include "wn.mm"
include "3nn.mm"
include "8nn.mm"
include "dec0h.mm"
include "cmul.mm"
include "caddc.mm"
include "ax-1cn.mm"
include "mulid1i.mm"
include "addid2i.mm"
include "oveq12i.mm"
include "1p1e2.mm"
include "eqtri.mm"
include "3cn.mm"
include "oveq1i.mm"
include "8cn.mm"
include "8p3e11.mm"
include "addcomli.mm"
include "decmac.mm"
include "1nn.mm"
include "8lt10.mm"
include "declti.mm"
include "ndvdsi.mm"
include "cprime.mm"
include "wb.mm"
include "13prm.mm"
include "coprm.mm"
include "mpbi.mm"
include "2cn.mm"
include "mulid2i.mm"
include "addid1i.mm"
include "2p1e3.mm"
include "3p1e4.mm"
include "3eqtri.mm"
include "decma2c.mm"
include "gcdi.mm"
include "3t2e6.mm"
include "mulcomli.mm"
include "6p2e8.mm"
include "4cn.mm"
include "4t2e8.mm"
include "8p1e9.mm"
include "4p3e7.mm"
include "oveq2i.mm"
include "7nn0.mm"
include "8t4e32.mm"
include "7cn.mm"
include "7p2e9.mm"
include "decaddi.mm"
include "9cn.mm"
include "9t4e36.mm"
include "6p4e10.mm"
include "decaddci2.mm"
include "9t2e18.mm"
include "8p8e16.mm"
include "decaddci.mm"
include "2t0e0.mm"
include "nn0cni.mm"
include "8p4e12.mm"
include "6cn.mm"
include "9p6e15.mm"
include "eqtr4i.mm"
include "gcdmodi.mm"

theorem 1259lem5
  let cN: class N
  assume 1259prm.1: |- N = ; ; ; 1 2 5 9


  assert |- ( ( ( 2 ^ ; 3 4 ) - 1 ) gcd N ) = 1

  proof
    c8
    c6
    cdc
    #
    c9
    cdc
    #
    c1
    c2
    c3
    c4
    cdc
    #
    cexp
    co
    #
    c1
    cmin
    co
    #
    cN
    @3
    cn
    wcel
    #
    @4
    cn0
    wcel
    c2
    cn
    wcel
    @2
    cn0
    wcel
    @5
    2nn
    c3
    c4
    3nn0
    4nn0
    deccl
    #
    c2
    @2
    nnexpcl
    mp2an
    #
    @3
    nnm1nn0
    ax-mp
    @0
    c9
    c8
    c6
    8nn0
    6nn0
    deccl
    #
    9nn0
    deccl
    #
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
    #
    cn
    1259prm.1
    @11
    c9
    @10
    c5
    c1
    c2
    1nn0
    2nn0
    deccl
    5nn0
    deccl
    9nn
    decnncl
    eqeltri
    #
    @3
    c1
    c8
    c7
    cdc
    #
    cc0
    cdc
    @1
    cN
    @13
    @7
    1nn0
    @9
    cN
    1259prm.1
    1259lem2
    @0
    @14
    @1
    @8
    c8
    c6
    c7
    @0
    8nn0
    6nn0
    6p1e7
    @0
    eqid
    #
    decsuc
    @1
    eqid
    #
    decsucc
    modsubi
    c3
    c9
    cdc
    #
    cc0
    cdc
    #
    c1
    c1
    cN
    @1
    1nn0
    @17
    cc0
    c3
    c9
    3nn0
    9nn0
    deccl
    #
    0nn0
    deccl
    #
    @9
    c8
    c9
    cdc
    #
    c1
    c2
    @1
    @18
    2nn0
    c8
    c9
    8nn0
    9nn0
    deccl
    #
    @20
    @2
    c1
    c4
    @18
    @21
    4nn0
    @6
    @22
    c2
    c1
    cdc
    #
    c1
    c2
    @21
    @2
    2nn0
    c2
    c1
    2nn0
    1nn0
    deccl
    #
    @6
    c1
    c3
    cdc
    #
    c1
    c1
    @2
    @23
    1nn0
    c1
    c3
    1nn0
    3nn0
    deccl
    #
    @24
    @23
    @25
    cgcd
    co
    #
    @25
    @23
    cgcd
    co
    #
    c1
    @23
    cz
    wcel
    #
    @25
    cz
    wcel
    @27
    @28
    wceq
    @23
    @24
    nn0zi
    #
    @25
    @26
    nn0zi
    @23
    @25
    gcdcom
    mp2an
    @25
    @23
    cdvds
    wbr
    wn
    #
    @28
    c1
    wceq
    #
    @25
    @23
    c1
    c8
    c1
    c3
    1nn0
    3nn
    decnncl
    1nn0
    8nn
    c1
    c3
    cc0
    c8
    c1
    c2
    c1
    c1
    @25
    c8
    1nn0
    3nn0
    0nn0
    8nn0
    @25
    eqid
    #
    c8
    8nn0
    dec0h
    #
    1nn0
    1nn0
    1nn0
    c1
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
    c1
    c1
    caddc
    co
    c2
    @35
    c1
    @36
    c1
    caddc
    c1
    ax-1cn
    mulid1i
    #
    c1
    ax-1cn
    addid2i
    oveq12i
    1p1e2
    eqtri
    c3
    c1
    cmul
    co
    #
    c8
    caddc
    co
    c3
    c8
    caddc
    co
    c1
    c1
    cdc
    #
    @38
    c3
    c8
    caddc
    c3
    3cn
    mulid1i
    oveq1i
    c8
    c3
    @39
    8cn
    3cn
    8p3e11
    addcomli
    eqtri
    decmac
    c1
    c3
    c8
    1nn
    3nn0
    8nn0
    8lt10
    declti
    ndvdsi
    @25
    cprime
    wcel
    @29
    @31
    @32
    wb
    13prm
    @30
    @25
    @23
    coprm
    mp2an
    mpbi
    eqtri
    c2
    c1
    c1
    c3
    c1
    c3
    c4
    cc0
    @23
    @25
    2nn0
    1nn0
    1nn0
    3nn0
    @23
    eqid
    #
    @33
    1nn0
    4nn0
    0nn0
    c1
    c2
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
    c2
    c1
    caddc
    co
    c3
    @41
    c2
    @42
    c1
    caddc
    c2
    2cn
    mulid2i
    c1
    ax-1cn
    addid1i
    oveq12i
    2p1e3
    eqtri
    @35
    c3
    caddc
    co
    c1
    c3
    caddc
    co
    c4
    cc0
    c4
    cdc
    @35
    c1
    c3
    caddc
    @37
    oveq1i
    c3
    c1
    c4
    3cn
    ax-1cn
    3p1e4
    addcomli
    c4
    4nn0
    dec0h
    3eqtri
    decma2c
    gcdi
    c3
    c4
    c2
    c1
    c2
    c8
    c9
    cc0
    @2
    @23
    3nn0
    4nn0
    2nn0
    1nn0
    @2
    eqid
    #
    @40
    2nn0
    9nn0
    0nn0
    c2
    c3
    cmul
    co
    #
    c2
    cc0
    caddc
    co
    #
    caddc
    co
    c6
    c2
    caddc
    co
    #
    c8
    @44
    c6
    @45
    c2
    caddc
    c3
    c2
    c6
    3cn
    2cn
    3t2e6
    mulcomli
    #
    c2
    2cn
    addid1i
    oveq12i
    6p2e8
    eqtri
    c2
    c4
    cmul
    co
    #
    c1
    caddc
    co
    c8
    c1
    caddc
    co
    c9
    cc0
    c9
    cdc
    #
    @48
    c8
    c1
    caddc
    c4
    c2
    c8
    4cn
    2cn
    4t2e8
    mulcomli
    oveq1i
    8p1e9
    c9
    9nn0
    dec0h
    #
    3eqtri
    decma2c
    gcdi
    c8
    c9
    c3
    c4
    c4
    @17
    cc0
    c4
    @21
    @2
    8nn0
    9nn0
    3nn0
    4nn0
    @21
    eqid
    #
    @43
    4nn0
    0nn0
    4nn0
    c4
    c8
    cmul
    co
    #
    c3
    c4
    caddc
    co
    #
    caddc
    co
    @52
    c7
    caddc
    co
    @17
    @53
    c7
    @52
    caddc
    c4
    c3
    c7
    4cn
    3cn
    4p3e7
    addcomli
    oveq2i
    c3
    c2
    c9
    @52
    c7
    3nn0
    2nn0
    7nn0
    c8
    c4
    c3
    c2
    cdc
    8cn
    4cn
    8t4e32
    mulcomli
    c7
    c2
    c9
    7cn
    2cn
    7p2e9
    addcomli
    decaddi
    eqtri
    c3
    c6
    c4
    c4
    c9
    cmul
    co
    c4
    3nn0
    6nn0
    4nn0
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
    6p4e10
    decaddci2
    decma2c
    gcdi
    @17
    cc0
    c8
    c9
    c2
    @0
    c9
    cc0
    @18
    @21
    @19
    0nn0
    8nn0
    9nn0
    @18
    eqid
    #
    @51
    2nn0
    9nn0
    0nn0
    c3
    c9
    cc0
    c8
    c2
    c8
    c6
    c2
    @17
    c8
    cc0
    caddc
    co
    #
    3nn0
    9nn0
    0nn0
    8nn0
    @17
    eqid
    @55
    c8
    cc0
    c8
    cdc
    c8
    8cn
    addid1i
    @34
    eqtri
    2nn0
    6nn0
    2nn0
    @44
    cc0
    c2
    caddc
    co
    #
    caddc
    co
    @46
    c8
    @44
    c6
    @56
    c2
    caddc
    @47
    c2
    2cn
    addid2i
    oveq12i
    6p2e8
    eqtri
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
    decma2c
    c2
    cc0
    cmul
    co
    #
    c9
    caddc
    co
    cc0
    c9
    caddc
    co
    c9
    @49
    @57
    cc0
    c9
    caddc
    2t0e0
    oveq1i
    c9
    9cn
    addid2i
    @50
    3eqtri
    decma2c
    gcdi
    c1
    @1
    cmul
    co
    @18
    caddc
    co
    @12
    cN
    @0
    c9
    @17
    cc0
    c1
    @11
    c9
    cc0
    @1
    @18
    @8
    9nn0
    @19
    0nn0
    @16
    @54
    1nn0
    9nn0
    0nn0
    c8
    c6
    c3
    c9
    c1
    @10
    c5
    c1
    @0
    @17
    cc0
    caddc
    co
    8nn0
    6nn0
    3nn0
    9nn0
    @15
    @17
    @17
    @19
    nn0cni
    addid1i
    1nn0
    5nn0
    1nn0
    c1
    c8
    cmul
    co
    #
    c3
    c1
    caddc
    co
    #
    caddc
    co
    c8
    c4
    caddc
    co
    @10
    @58
    c8
    @59
    c4
    caddc
    c8
    8cn
    mulid2i
    3p1e4
    oveq12i
    8p4e12
    eqtri
    c1
    c6
    cmul
    co
    #
    c9
    caddc
    co
    c6
    c9
    caddc
    co
    c1
    c5
    cdc
    #
    @60
    c6
    c9
    caddc
    c6
    6cn
    mulid2i
    oveq1i
    c9
    c6
    @61
    9cn
    6cn
    9p6e15
    addcomli
    eqtri
    decma2c
    c1
    c9
    cmul
    co
    #
    cc0
    caddc
    co
    c9
    cc0
    caddc
    co
    c9
    @49
    @62
    c9
    cc0
    caddc
    c9
    9cn
    mulid2i
    oveq1i
    c9
    9cn
    addid1i
    @50
    3eqtri
    decma2c
    1259prm.1
    eqtr4i
    gcdi
    gcdmodi
end
