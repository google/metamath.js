include "c3.mm"
include "c4.mm"
include "cv.mm"
include "cexp.mm"
include "co.mm"
include "c2.mm"
include "caddc.mm"
include "cdvds.mm"
include "wbr.mm"
include "cc0.mm"
include "c1.mm"
include "wceq.mm"
include "oveq2.mm"
include "oveq1d.mm"
include "breq2d.mm"
include "cz.mm"
include "wcel.mm"
include "3z.mm"
include "iddvds.mm"
include "ax-mp.mm"
include "4nn0.mm"
include "numexp0.mm"
include "oveq1i.mm"
include "1p2e3.mm"
include "eqtri.mm"
include "breqtrri.mm"
include "cn0.mm"
include "wa.mm"
include "cmul.mm"
include "cmin.mm"
include "a1i.mm"
include "id.mm"
include "nn0expcld.mm"
include "nn0zd.mm"
include "adantr.mm"
include "2z.mm"
include "zaddcld.mm"
include "4z.mm"
include "simpr.mm"
include "dvdsmultr1d.mm"
include "dvdsmul1.mm"
include "mp2an.mm"
include "simpl.mm"
include "zmulcld.mm"
include "dvds2subd.mm"
include "nn0cnd.mm"
include "2cnd.mm"
include "cc.mm"
include "4cn.mm"
include "adddird.mm"
include "3cn.mm"
include "2cn.mm"
include "mulcomi.mm"
include "oveq2d.mm"
include "expp1d.mm"
include "ax-1cn.mm"
include "3p1e4.mm"
include "addcomli.mm"
include "eqcomi.mm"
include "pncan3oi.mm"
include "oveq2i.mm"
include "subdii.mm"
include "2t1e2.mm"
include "3eqtr3ri.mm"
include "oveq12d.mm"
include "mulcld.mm"
include "addsubassd.mm"
include "eqtr4d.mm"
include "3eqtr4rd.mm"
include "breqtrrd.mm"
include "ex.mm"
include "nn0ind.mm"

theorem ex-ind-dvds
  let cN: class N
  let vk: setvar k
  let vn: setvar n


  assert |- ( N e. NN0 -> 3 || ( ( 4 ^ N ) + 2 ) )

  proof
    c3
    c4
    vk
    cv
    #
    cexp
    co
    #
    c2
    caddc
    co
    #
    cdvds
    wbr
    c3
    c4
    cc0
    cexp
    co
    #
    c2
    caddc
    co
    #
    cdvds
    wbr
    c3
    c4
    vn
    cv
    #
    cexp
    co
    #
    c2
    caddc
    co
    #
    cdvds
    wbr
    #
    c3
    c4
    @5
    c1
    caddc
    co
    #
    cexp
    co
    #
    c2
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
    c2
    caddc
    co
    #
    cdvds
    wbr
    vk
    vn
    cN
    @0
    cc0
    wceq
    #
    @2
    @4
    c3
    cdvds
    @15
    @1
    @3
    c2
    caddc
    @0
    cc0
    c4
    cexp
    oveq2
    oveq1d
    breq2d
    @0
    @5
    wceq
    #
    @2
    @7
    c3
    cdvds
    @16
    @1
    @6
    c2
    caddc
    @0
    @5
    c4
    cexp
    oveq2
    oveq1d
    breq2d
    @0
    @9
    wceq
    #
    @2
    @11
    c3
    cdvds
    @17
    @1
    @10
    c2
    caddc
    @0
    @9
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
    @14
    c3
    cdvds
    @18
    @1
    @13
    c2
    caddc
    @0
    cN
    c4
    cexp
    oveq2
    oveq1d
    breq2d
    c3
    c3
    @4
    cdvds
    c3
    cz
    wcel
    #
    c3
    c3
    cdvds
    wbr
    3z
    c3
    iddvds
    ax-mp
    @4
    c1
    c2
    caddc
    co
    c3
    @3
    c1
    c2
    caddc
    c4
    4nn0
    numexp0
    oveq1i
    1p2e3
    eqtri
    breqtrri
    @5
    cn0
    wcel
    #
    @8
    @12
    @20
    @8
    wa
    #
    c3
    @7
    c4
    cmul
    co
    #
    c3
    c2
    cmul
    co
    #
    cmin
    co
    #
    @11
    cdvds
    @21
    c3
    @22
    @23
    @19
    @21
    3z
    a1i
    #
    @21
    c3
    @7
    c4
    @25
    @21
    @6
    c2
    @20
    @6
    cz
    wcel
    @8
    @20
    @6
    @20
    c4
    @5
    c4
    cn0
    wcel
    #
    @20
    4nn0
    a1i
    @20
    id
    #
    nn0expcld
    #
    nn0zd
    adantr
    c2
    cz
    wcel
    #
    @21
    2z
    a1i
    #
    zaddcld
    c4
    cz
    wcel
    @21
    4z
    a1i
    #
    @20
    @8
    simpr
    dvdsmultr1d
    c3
    @23
    cdvds
    wbr
    #
    @21
    @19
    @29
    @32
    3z
    2z
    c3
    c2
    dvdsmul1
    mp2an
    a1i
    @21
    @7
    c4
    @21
    @6
    c2
    @21
    @6
    @21
    c4
    @5
    @26
    @21
    4nn0
    a1i
    @20
    @8
    simpl
    nn0expcld
    nn0zd
    @30
    zaddcld
    @31
    zmulcld
    @21
    c3
    c2
    @25
    @30
    zmulcld
    dvds2subd
    @20
    @11
    @24
    wceq
    @8
    @20
    @22
    c2
    c3
    cmul
    co
    #
    cmin
    co
    @6
    c4
    cmul
    co
    #
    c2
    c4
    cmul
    co
    #
    caddc
    co
    #
    @33
    cmin
    co
    #
    @24
    @11
    @20
    @22
    @36
    @33
    cmin
    @20
    @6
    c2
    c4
    @20
    @6
    @28
    nn0cnd
    #
    @20
    2cnd
    #
    c4
    cc
    wcel
    @20
    4cn
    a1i
    #
    adddird
    oveq1d
    @20
    @23
    @33
    @22
    cmin
    @23
    @33
    wceq
    @20
    c3
    c2
    3cn
    2cn
    mulcomi
    a1i
    oveq2d
    @20
    @11
    @34
    @35
    @33
    cmin
    co
    #
    caddc
    co
    @37
    @20
    @10
    @34
    c2
    @41
    caddc
    @20
    c4
    @5
    @40
    @27
    expp1d
    c2
    @41
    wceq
    @20
    c2
    c4
    c3
    cmin
    co
    #
    cmul
    co
    c2
    c1
    cmul
    co
    @41
    c2
    @42
    c1
    c2
    cmul
    @42
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
    @43
    c3
    cmin
    @43
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
    c2
    c4
    c3
    2cn
    4cn
    3cn
    subdii
    2t1e2
    3eqtr3ri
    a1i
    oveq12d
    @20
    @34
    @35
    @33
    @20
    @6
    c4
    @38
    @40
    mulcld
    @20
    c2
    c4
    @39
    @40
    mulcld
    @20
    c2
    c3
    @39
    c3
    cc
    wcel
    @20
    3cn
    a1i
    mulcld
    addsubassd
    eqtr4d
    3eqtr4rd
    adantr
    breqtrrd
    ex
    nn0ind
end
