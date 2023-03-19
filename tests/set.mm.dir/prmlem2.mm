include "c5.mm"
include "c7.mm"
include "c9.mm"
include "c1.mm"
include "cdc.mm"
include "c3.mm"
include "c2.mm"
include "cv.mm"
include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "cprime.mm"
include "csn.mm"
include "cdif.mm"
include "cexp.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "cdvds.mm"
include "wn.mm"
include "wi.mm"
include "clt.mm"
include "cr.mm"
include "eluzelre.mm"
include "resqcld.mm"
include "eluzle.mm"
include "cc0.mm"
include "2nn0.mm"
include "9nn0.mm"
include "deccl.mm"
include "nn0rei.mm"
include "nn0ge0i.mm"
include "le2sq2.mm"
include "mpanl12.mm"
include "syl2anc.mm"
include "nnrei.mm"
include "resqcli.mm"
include "w3a.mm"
include "c8.mm"
include "c4.mm"
include "cmul.mm"
include "nn0cni.mm"
include "sqvali.mm"
include "c6.mm"
include "eqid.mm"
include "1nn0.mm"
include "6nn0.mm"
include "5nn0.mm"
include "8nn0.mm"
include "caddc.mm"
include "2timesi.mm"
include "2p2e4.mm"
include "oveq1i.mm"
include "4p1e5.mm"
include "eqtri.mm"
include "9p9e18.mm"
include "decaddc.mm"
include "5p2e7.mm"
include "7p1e8.mm"
include "4nn0.mm"
include "8p6e14.mm"
include "9t2e18.mm"
include "1p1e2.mm"
include "8p8e16.mm"
include "decaddci.mm"
include "9t9e81.mm"
include "decmul2c.mm"
include "decmul1c.mm"
include "breqtrri.mm"
include "ltletr.mm"
include "mpani.mm"
include "mp3an12.mm"
include "sylc.mm"
include "wb.mm"
include "ltnle.mm"
include "sylancr.mm"
include "mpbid.mm"
include "pm2.21d.mm"
include "adantld.mm"
include "adantl.mm"
include "9nn.mm"
include "3nn.mm"
include "1lt9.mm"
include "1lt3.mm"
include "9t3e27.mm"
include "nprmi.mm"
include "pm2.21i.mm"
include "7nn0.mm"
include "7p2e9.mm"
include "decaddi.mm"
include "prmlem0.mm"
include "5nn.mm"
include "1lt5.mm"
include "5t5e25.mm"
include "a1i.mm"
include "3nn0.mm"
include "3p2e5.mm"
include "7nn.mm"
include "1lt7.mm"
include "7t3e21.mm"
include "1p2e3.mm"
include "9p2e11.mm"
include "5t3e15.mm"
include "9nprm.mm"
include "prmlem1a.mm"

theorem prmlem2
  let cN: class N
  let vx: setvar x
  assume prmlem2.n: |- N e. NN
  assume prmlem2.lt: |- N < ; ; 8 4 1
  assume prmlem2.gt: |- 1 < N
  assume prmlem2.2: |- -. 2 || N
  assume prmlem2.3: |- -. 3 || N
  assume prmlem2.5: |- -. 5 || N
  assume prmlem2.7: |- -. 7 || N
  assume prmlem2.11: |- -. ; 1 1 || N
  assume prmlem2.13: |- -. ; 1 3 || N
  assume prmlem2.17: |- -. ; 1 7 || N
  assume prmlem2.19: |- -. ; 1 9 || N
  assume prmlem2.23: |- -. ; 2 3 || N


  assert |- N e. Prime

  proof
    vx
    cN
    prmlem2.n
    prmlem2.gt
    prmlem2.2
    prmlem2.3
    vx
    c5
    c7
    cN
    vx
    c7
    c9
    cN
    vx
    c9
    c1
    c1
    cdc
    #
    cN
    vx
    @0
    c1
    c3
    cdc
    #
    cN
    vx
    @1
    c1
    c5
    cdc
    #
    cN
    vx
    @2
    c1
    c7
    cdc
    #
    cN
    vx
    @3
    c1
    c9
    cdc
    #
    cN
    vx
    @4
    c2
    c1
    cdc
    #
    cN
    vx
    @5
    c2
    c3
    cdc
    #
    cN
    vx
    @6
    c2
    c5
    cdc
    #
    cN
    vx
    @7
    c2
    c7
    cdc
    #
    cN
    vx
    @8
    c2
    c9
    cdc
    #
    cN
    vx
    cv
    #
    @9
    cuz
    cfv
    wcel
    #
    @10
    cprime
    c2
    csn
    cdif
    wcel
    #
    @10
    c2
    cexp
    co
    #
    cN
    cle
    wbr
    #
    wa
    @10
    cN
    cdvds
    wbr
    wn
    #
    wi
    c2
    @9
    cdvds
    wbr
    wn
    @11
    @14
    @15
    @12
    @11
    @14
    @15
    @11
    cN
    @13
    clt
    wbr
    #
    @14
    wn
    #
    @11
    @13
    cr
    wcel
    #
    @9
    c2
    cexp
    co
    #
    @13
    cle
    wbr
    #
    @16
    @11
    @10
    @9
    @10
    eluzelre
    #
    resqcld
    #
    @11
    @10
    cr
    wcel
    #
    @9
    @10
    cle
    wbr
    #
    @20
    @21
    @9
    @10
    eluzle
    @9
    cr
    wcel
    cc0
    @9
    cle
    wbr
    @23
    @24
    wa
    @20
    @9
    c2
    c9
    2nn0
    9nn0
    deccl
    #
    nn0rei
    #
    @9
    @25
    nn0ge0i
    @9
    @10
    le2sq2
    mpanl12
    syl2anc
    cN
    cr
    wcel
    #
    @19
    cr
    wcel
    #
    @18
    @20
    @16
    wi
    cN
    prmlem2.n
    nnrei
    #
    @9
    @26
    resqcli
    @27
    @28
    @18
    w3a
    cN
    @19
    clt
    wbr
    @20
    @16
    cN
    c8
    c4
    cdc
    #
    c1
    cdc
    #
    @19
    clt
    prmlem2.lt
    @19
    @9
    @9
    cmul
    co
    @31
    @9
    @9
    @25
    nn0cni
    #
    sqvali
    c2
    c9
    @30
    c1
    @9
    c2
    c6
    cdc
    #
    @9
    @25
    2nn0
    9nn0
    @9
    eqid
    #
    1nn0
    c2
    c6
    2nn0
    6nn0
    deccl
    c5
    c8
    c2
    c6
    c8
    c4
    c2
    @9
    cmul
    co
    #
    @33
    5nn0
    8nn0
    2nn0
    6nn0
    @35
    @9
    @9
    caddc
    co
    c5
    c8
    cdc
    @9
    @32
    2timesi
    c2
    c9
    c2
    c9
    c5
    c8
    @9
    @9
    2nn0
    9nn0
    2nn0
    9nn0
    @34
    @34
    c2
    c2
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
    c5
    @36
    c4
    c1
    caddc
    2p2e4
    oveq1i
    4p1e5
    eqtri
    8nn0
    9p9e18
    decaddc
    eqtri
    @33
    eqid
    c5
    c2
    caddc
    co
    #
    c1
    caddc
    co
    c7
    c1
    caddc
    co
    c8
    @37
    c7
    c1
    caddc
    5p2e7
    oveq1i
    7p1e8
    eqtri
    4nn0
    8p6e14
    decaddc
    c2
    c9
    @33
    c1
    c9
    c8
    @9
    9nn0
    2nn0
    9nn0
    @34
    1nn0
    8nn0
    c1
    c8
    c6
    c2
    c9
    c2
    cmul
    co
    c8
    1nn0
    8nn0
    8nn0
    9t2e18
    1p1e2
    6nn0
    8p8e16
    decaddci
    9t9e81
    decmul2c
    decmul1c
    eqtri
    breqtrri
    cN
    @19
    @13
    ltletr
    mpani
    mp3an12
    sylc
    @11
    @27
    @18
    @16
    @17
    wb
    @29
    @22
    cN
    @13
    ltnle
    sylancr
    mpbid
    pm2.21d
    adantld
    adantl
    @8
    cprime
    wcel
    @8
    cN
    cdvds
    wbr
    wn
    c9
    c3
    @8
    9nn
    3nn
    1lt9
    1lt3
    9t3e27
    nprmi
    pm2.21i
    c2
    c7
    c9
    @8
    c2
    2nn0
    7nn0
    2nn0
    @8
    eqid
    7p2e9
    decaddi
    prmlem0
    @7
    cprime
    wcel
    @7
    cN
    cdvds
    wbr
    wn
    c5
    c5
    @7
    5nn
    5nn
    1lt5
    1lt5
    5t5e25
    nprmi
    pm2.21i
    c2
    c5
    c7
    @7
    c2
    2nn0
    5nn0
    2nn0
    @7
    eqid
    5p2e7
    decaddi
    prmlem0
    @6
    cN
    cdvds
    wbr
    wn
    @6
    cprime
    wcel
    prmlem2.23
    a1i
    c2
    c3
    c5
    @6
    c2
    2nn0
    3nn0
    2nn0
    @6
    eqid
    3p2e5
    decaddi
    prmlem0
    @5
    cprime
    wcel
    @5
    cN
    cdvds
    wbr
    wn
    c7
    c3
    @5
    7nn
    3nn
    1lt7
    1lt3
    7t3e21
    nprmi
    pm2.21i
    c2
    c1
    c3
    @5
    c2
    2nn0
    1nn0
    2nn0
    @5
    eqid
    1p2e3
    decaddi
    prmlem0
    @4
    cN
    cdvds
    wbr
    wn
    @4
    cprime
    wcel
    prmlem2.19
    a1i
    c1
    c9
    c1
    c2
    @4
    c2
    1nn0
    9nn0
    2nn0
    @4
    eqid
    1p1e2
    1nn0
    9p2e11
    decaddci
    prmlem0
    @3
    cN
    cdvds
    wbr
    wn
    @3
    cprime
    wcel
    prmlem2.17
    a1i
    c1
    c7
    c9
    @3
    c2
    1nn0
    7nn0
    2nn0
    @3
    eqid
    7p2e9
    decaddi
    prmlem0
    @2
    cprime
    wcel
    @2
    cN
    cdvds
    wbr
    wn
    c5
    c3
    @2
    5nn
    3nn
    1lt5
    1lt3
    5t3e15
    nprmi
    pm2.21i
    c1
    c5
    c7
    @2
    c2
    1nn0
    5nn0
    2nn0
    @2
    eqid
    5p2e7
    decaddi
    prmlem0
    @1
    cN
    cdvds
    wbr
    wn
    @1
    cprime
    wcel
    prmlem2.13
    a1i
    c1
    c3
    c5
    @1
    c2
    1nn0
    3nn0
    2nn0
    @1
    eqid
    3p2e5
    decaddi
    prmlem0
    @0
    cN
    cdvds
    wbr
    wn
    @0
    cprime
    wcel
    prmlem2.11
    a1i
    c1
    c1
    c3
    @0
    c2
    1nn0
    1nn0
    2nn0
    @0
    eqid
    1p2e3
    decaddi
    prmlem0
    c9
    cprime
    wcel
    c9
    cN
    cdvds
    wbr
    wn
    9nprm
    pm2.21i
    9p2e11
    prmlem0
    c7
    cN
    cdvds
    wbr
    wn
    c7
    cprime
    wcel
    prmlem2.7
    a1i
    7p2e9
    prmlem0
    c5
    cN
    cdvds
    wbr
    wn
    c5
    cprime
    wcel
    prmlem2.5
    a1i
    5p2e7
    prmlem0
    prmlem1a
end
