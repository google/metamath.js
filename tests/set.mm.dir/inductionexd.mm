include "c3.mm"
include "c4.mm"
include "cv.mm"
include "cexp.mm"
include "co.mm"
include "c5.mm"
include "caddc.mm"
include "cdvds.mm"
include "wbr.mm"
include "c1.mm"
include "wceq.mm"
include "oveq2.mm"
include "oveq1d.mm"
include "breq2d.mm"
include "cz.mm"
include "wcel.mm"
include "w3a.mm"
include "cmul.mm"
include "3z.mm"
include "cn0.mm"
include "4z.mm"
include "1nn0.mm"
include "zexpcl.mm"
include "mp2an.mm"
include "5nn.mm"
include "nnzi.mm"
include "zaddcl.mm"
include "3pm3.2i.mm"
include "c9.mm"
include "3t3e9.mm"
include "4nn0.mm"
include "numexp1.mm"
include "oveq1i.mm"
include "5cn.mm"
include "4cn.mm"
include "5p4e9.mm"
include "addcomli.mm"
include "eqtri.mm"
include "eqtr4i.mm"
include "dvds0lem.mm"
include "cn.mm"
include "wa.mm"
include "cmin.mm"
include "a1i.mm"
include "4nn.mm"
include "nnnn0.mm"
include "nnexpcld.mm"
include "nnzd.mm"
include "adantr.mm"
include "zaddcld.mm"
include "simpr.mm"
include "dvdsmultr1d.mm"
include "dvdsmul1.mm"
include "zmulcld.mm"
include "dvds2subd.mm"
include "cdc.mm"
include "nncnd.mm"
include "cc.mm"
include "adddird.mm"
include "3cn.mm"
include "5t3e15.mm"
include "mulcomli.mm"
include "oveq2d.mm"
include "expp1d.mm"
include "ax-1cn.mm"
include "3p1e4.mm"
include "eqcomi.mm"
include "pncan3oi.mm"
include "oveq2i.mm"
include "subdii.mm"
include "mulid1i.mm"
include "3eqtr3ri.mm"
include "oveq12d.mm"
include "mulcld.mm"
include "5nn0.mm"
include "deccl.mm"
include "nn0cni.mm"
include "addsubassd.mm"
include "eqtr4d.mm"
include "3eqtr4rd.mm"
include "breqtrrd.mm"
include "ex.mm"
include "nnind.mm"

theorem inductionexd
  let cN: class N
  let vk: setvar k
  let vn: setvar n


  assert |- ( N e. NN -> 3 || ( ( 4 ^ N ) + 5 ) )

  proof
    c3
    c4
    vk
    cv
    #
    cexp
    co
    #
    c5
    caddc
    co
    #
    cdvds
    wbr
    c3
    c4
    c1
    cexp
    co
    #
    c5
    caddc
    co
    #
    cdvds
    wbr
    #
    c3
    c4
    vn
    cv
    #
    cexp
    co
    #
    c5
    caddc
    co
    #
    cdvds
    wbr
    #
    c3
    c4
    @6
    c1
    caddc
    co
    #
    cexp
    co
    #
    c5
    caddc
    co
    #
    cdvds
    wbr
    #
    c3
    c4
    cN
    cexp
    co
    #
    c5
    caddc
    co
    #
    cdvds
    wbr
    vk
    vn
    cN
    @0
    c1
    wceq
    #
    @2
    @4
    c3
    cdvds
    @16
    @1
    @3
    c5
    caddc
    @0
    c1
    c4
    cexp
    oveq2
    oveq1d
    breq2d
    @0
    @6
    wceq
    #
    @2
    @8
    c3
    cdvds
    @17
    @1
    @7
    c5
    caddc
    @0
    @6
    c4
    cexp
    oveq2
    oveq1d
    breq2d
    @0
    @10
    wceq
    #
    @2
    @12
    c3
    cdvds
    @18
    @1
    @11
    c5
    caddc
    @0
    @10
    c4
    cexp
    oveq2
    oveq1d
    breq2d
    @0
    cN
    wceq
    #
    @2
    @15
    c3
    cdvds
    @19
    @1
    @14
    c5
    caddc
    @0
    cN
    c4
    cexp
    oveq2
    oveq1d
    breq2d
    c3
    cz
    wcel
    #
    @20
    @4
    cz
    wcel
    #
    w3a
    c3
    c3
    cmul
    co
    #
    @4
    wceq
    @5
    @20
    @20
    @21
    3z
    3z
    @3
    cz
    wcel
    #
    c5
    cz
    wcel
    #
    @21
    c4
    cz
    wcel
    #
    c1
    cn0
    wcel
    @23
    4z
    1nn0
    c4
    c1
    zexpcl
    mp2an
    c5
    5nn
    nnzi
    #
    @3
    c5
    zaddcl
    mp2an
    3pm3.2i
    @22
    c9
    @4
    3t3e9
    @4
    c4
    c5
    caddc
    co
    c9
    @3
    c4
    c5
    caddc
    c4
    4nn0
    numexp1
    oveq1i
    c5
    c4
    c9
    5cn
    4cn
    5p4e9
    addcomli
    eqtri
    eqtr4i
    c3
    c3
    @4
    dvds0lem
    mp2an
    @6
    cn
    wcel
    #
    @9
    @13
    @27
    @9
    wa
    #
    c3
    @8
    c4
    cmul
    co
    #
    c3
    c5
    cmul
    co
    #
    cmin
    co
    #
    @12
    cdvds
    @28
    c3
    @29
    @30
    @20
    @28
    3z
    a1i
    #
    @28
    c3
    @8
    c4
    @32
    @28
    @7
    c5
    @27
    @7
    cz
    wcel
    @9
    @27
    @7
    @27
    c4
    @6
    c4
    cn
    wcel
    @27
    4nn
    a1i
    @6
    nnnn0
    #
    nnexpcld
    #
    nnzd
    adantr
    @24
    @28
    @26
    a1i
    #
    zaddcld
    #
    @25
    @28
    4z
    a1i
    #
    @27
    @9
    simpr
    dvdsmultr1d
    c3
    @30
    cdvds
    wbr
    #
    @28
    @20
    @24
    @38
    3z
    @26
    c3
    c5
    dvdsmul1
    mp2an
    a1i
    @28
    @8
    c4
    @36
    @37
    zmulcld
    @28
    c3
    c5
    @32
    @35
    zmulcld
    dvds2subd
    @27
    @12
    @31
    wceq
    @9
    @27
    @29
    c1
    c5
    cdc
    #
    cmin
    co
    @7
    c4
    cmul
    co
    #
    c5
    c4
    cmul
    co
    #
    caddc
    co
    #
    @39
    cmin
    co
    #
    @31
    @12
    @27
    @29
    @42
    @39
    cmin
    @27
    @7
    c5
    c4
    @27
    @7
    @34
    nncnd
    #
    c5
    cc
    wcel
    @27
    5cn
    a1i
    #
    c4
    cc
    wcel
    @27
    4cn
    a1i
    #
    adddird
    oveq1d
    @27
    @30
    @39
    @29
    cmin
    @30
    @39
    wceq
    @27
    c5
    c3
    @39
    5cn
    3cn
    5t3e15
    mulcomli
    a1i
    oveq2d
    @27
    @12
    @40
    @41
    @39
    cmin
    co
    #
    caddc
    co
    @43
    @27
    @11
    @40
    c5
    @47
    caddc
    @27
    c4
    @6
    @46
    @33
    expp1d
    c5
    @47
    wceq
    @27
    c5
    @41
    c5
    c3
    cmul
    co
    #
    cmin
    co
    #
    @47
    c5
    c4
    c3
    cmin
    co
    #
    cmul
    co
    c5
    c1
    cmul
    co
    @49
    c5
    @50
    c1
    c5
    cmul
    @50
    c1
    c3
    caddc
    co
    #
    c3
    cmin
    co
    c1
    c4
    @51
    c3
    cmin
    @51
    c4
    c3
    c1
    c4
    3cn
    ax-1cn
    3p1e4
    addcomli
    eqcomi
    oveq1i
    c1
    c3
    ax-1cn
    3cn
    pncan3oi
    eqtri
    oveq2i
    c5
    c4
    c3
    5cn
    4cn
    3cn
    subdii
    c5
    5cn
    mulid1i
    3eqtr3ri
    @39
    @48
    @41
    cmin
    @48
    @39
    5t3e15
    eqcomi
    oveq2i
    eqtr4i
    a1i
    oveq12d
    @27
    @40
    @41
    @39
    @27
    @7
    c4
    @44
    @46
    mulcld
    @27
    c5
    c4
    @45
    @46
    mulcld
    @39
    cc
    wcel
    @27
    @39
    c1
    c5
    1nn0
    5nn0
    deccl
    nn0cni
    a1i
    addsubassd
    eqtr4d
    3eqtr4rd
    adantr
    breqtrrd
    ex
    nnind
end
