include "cn.mm"
include "wcel.mm"
include "cfmtno.mm"
include "cfv.mm"
include "cdvds.mm"
include "wbr.mm"
include "cv.mm"
include "c2.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cexp.mm"
include "cmul.mm"
include "wceq.mm"
include "cn0.mm"
include "wrex.mm"
include "cuz.mm"
include "wo.mm"
include "wi.mm"
include "elnn1uz2.mm"
include "c5.mm"
include "c4.mm"
include "cprime.mm"
include "wb.mm"
include "5prm.mm"
include "dvdsprime.mm"
include "mpan.mm"
include "1nn0.mm"
include "a1i.mm"
include "wa.mm"
include "simpl.mm"
include "oveq1.mm"
include "oveq1d.mm"
include "adantl.mm"
include "eqeq12d.mm"
include "df-5.mm"
include "4cn.mm"
include "mulid2i.mm"
include "eqcomi.mm"
include "oveq1i.mm"
include "eqtri.mm"
include "rspcedvd.mm"
include "cc0.mm"
include "0nn0.mm"
include "mul02i.mm"
include "0p1e1.mm"
include "jaoi.mm"
include "syl6bi.mm"
include "fveq2.mm"
include "fmtno1.mm"
include "syl6eq.mm"
include "breq2d.mm"
include "1p1e2.mm"
include "oveq2d.mm"
include "sq2.mm"
include "eqeq2d.mm"
include "rexbidv.mm"
include "imbi12d.mm"
include "syl5ibr.mm"
include "w3a.mm"
include "fmtnofac2.mm"
include "id.mm"
include "2nn0.mm"
include "nn0mulcld.mm"
include "adantr.mm"
include "simpr.mm"
include "eqeqan12d.mm"
include "cc.mm"
include "eluzge2nn0.mm"
include "nn0cnd.mm"
include "add1p1.mm"
include "syl.mm"
include "eqcomd.mm"
include "2cnd.mm"
include "peano2nn0.mm"
include "expp1d.mm"
include "nn0expcld.mm"
include "mulcomd.mm"
include "3eqtrd.mm"
include "nn0cn.mm"
include "mulassd.mm"
include "eqtr4d.mm"
include "3ad2antl1.mm"
include "ex.mm"
include "rexlimdva.mm"
include "mpd.mm"
include "3exp.mm"
include "sylbi.mm"
include "3imp.mm"

theorem fmtnofac1
  let vk: setvar k
  let cM: class M
  let cN: class N
  let vn: setvar n
  let vx: setvar x

  disjoint M k
  disjoint N k
  disjoint M n
  disjoint k n
  disjoint N n
  disjoint k x
  assert |- ( ( N e. NN /\ M e. NN /\ M || ( FermatNo ` N ) ) -> E. k e. NN0 M = ( ( k x. ( 2 ^ ( N + 1 ) ) ) + 1 ) )

  proof
    cN
    cn
    wcel
    #
    cM
    cn
    wcel
    #
    cM
    cN
    cfmtno
    cfv
    #
    cdvds
    wbr
    #
    cM
    vk
    cv
    #
    c2
    cN
    c1
    caddc
    co
    #
    cexp
    co
    #
    cmul
    co
    #
    c1
    caddc
    co
    #
    wceq
    #
    vk
    cn0
    wrex
    #
    @0
    cN
    c1
    wceq
    #
    cN
    c2
    cuz
    cfv
    wcel
    #
    wo
    @1
    @3
    @10
    wi
    #
    wi
    #
    cN
    elnn1uz2
    @11
    @14
    @12
    @1
    @13
    @11
    cM
    c5
    cdvds
    wbr
    #
    cM
    @4
    c4
    cmul
    co
    #
    c1
    caddc
    co
    #
    wceq
    #
    vk
    cn0
    wrex
    #
    wi
    @1
    @15
    cM
    c5
    wceq
    #
    cM
    c1
    wceq
    #
    wo
    #
    @19
    c5
    cprime
    wcel
    @1
    @15
    @22
    wb
    5prm
    c5
    cM
    dvdsprime
    mpan
    @20
    @19
    @21
    @20
    @18
    c5
    c1
    c4
    cmul
    co
    #
    c1
    caddc
    co
    #
    wceq
    #
    vk
    c1
    cn0
    c1
    cn0
    wcel
    @20
    1nn0
    a1i
    @20
    @4
    c1
    wceq
    #
    wa
    cM
    c5
    @17
    @24
    @20
    @26
    simpl
    @26
    @17
    @24
    wceq
    @20
    @26
    @16
    @23
    c1
    caddc
    @4
    c1
    c4
    cmul
    oveq1
    oveq1d
    adantl
    eqeq12d
    @25
    @20
    c5
    c4
    c1
    caddc
    co
    @24
    df-5
    c4
    @23
    c1
    caddc
    @23
    c4
    c4
    4cn
    mulid2i
    eqcomi
    oveq1i
    eqtri
    a1i
    rspcedvd
    @21
    @18
    c1
    cc0
    c4
    cmul
    co
    #
    c1
    caddc
    co
    #
    wceq
    #
    vk
    cc0
    cn0
    cc0
    cn0
    wcel
    @21
    0nn0
    a1i
    @21
    @4
    cc0
    wceq
    #
    wa
    cM
    c1
    @17
    @28
    @21
    @30
    simpl
    @30
    @17
    @28
    wceq
    @21
    @30
    @16
    @27
    c1
    caddc
    @4
    cc0
    c4
    cmul
    oveq1
    oveq1d
    adantl
    eqeq12d
    @29
    @21
    @28
    c1
    @28
    cc0
    c1
    caddc
    co
    c1
    @27
    cc0
    c1
    caddc
    c4
    4cn
    mul02i
    oveq1i
    0p1e1
    eqtri
    eqcomi
    a1i
    rspcedvd
    jaoi
    syl6bi
    @11
    @3
    @15
    @10
    @19
    @11
    @2
    c5
    cM
    cdvds
    @11
    @2
    c1
    cfmtno
    cfv
    c5
    cN
    c1
    cfmtno
    fveq2
    fmtno1
    syl6eq
    breq2d
    @11
    @9
    @18
    vk
    cn0
    @11
    @8
    @17
    cM
    @11
    @7
    @16
    c1
    caddc
    @11
    @6
    c4
    @4
    cmul
    @11
    @6
    c2
    c2
    cexp
    co
    c4
    @11
    @5
    c2
    c2
    cexp
    @11
    @5
    c1
    c1
    caddc
    co
    c2
    cN
    c1
    c1
    caddc
    oveq1
    1p1e2
    syl6eq
    oveq2d
    sq2
    syl6eq
    oveq2d
    oveq1d
    eqeq2d
    rexbidv
    imbi12d
    syl5ibr
    @12
    @1
    @3
    @10
    @12
    @1
    @3
    w3a
    #
    cM
    vn
    cv
    #
    c2
    cN
    c2
    caddc
    co
    #
    cexp
    co
    #
    cmul
    co
    #
    c1
    caddc
    co
    #
    wceq
    #
    vn
    cn0
    wrex
    @10
    vn
    cM
    cN
    fmtnofac2
    @31
    @37
    @10
    vn
    cn0
    @31
    @32
    cn0
    wcel
    #
    wa
    #
    @37
    @10
    @39
    @37
    wa
    #
    @9
    @36
    @32
    c2
    cmul
    co
    #
    @6
    cmul
    co
    #
    c1
    caddc
    co
    #
    wceq
    vk
    @41
    cn0
    @39
    @41
    cn0
    wcel
    #
    @37
    @38
    @44
    @31
    @38
    @32
    c2
    @38
    id
    c2
    cn0
    wcel
    #
    @38
    2nn0
    a1i
    nn0mulcld
    adantl
    adantr
    @40
    @4
    @41
    wceq
    #
    cM
    @36
    @8
    @43
    @39
    @37
    simpr
    @46
    @7
    @42
    c1
    caddc
    @4
    @41
    @6
    cmul
    oveq1
    oveq1d
    eqeqan12d
    @40
    @35
    @42
    c1
    caddc
    @39
    @35
    @42
    wceq
    #
    @37
    @12
    @1
    @38
    @47
    @3
    @12
    @38
    wa
    #
    @35
    @32
    c2
    @6
    cmul
    co
    #
    cmul
    co
    @42
    @48
    @34
    @49
    @32
    cmul
    @12
    @34
    @49
    wceq
    @38
    @12
    @34
    c2
    @5
    c1
    caddc
    co
    #
    cexp
    co
    @6
    c2
    cmul
    co
    @49
    @12
    @33
    @50
    c2
    cexp
    @12
    @50
    @33
    @12
    cN
    cc
    wcel
    @50
    @33
    wceq
    @12
    cN
    cN
    eluzge2nn0
    #
    nn0cnd
    cN
    add1p1
    syl
    eqcomd
    oveq2d
    @12
    c2
    @5
    @12
    2cnd
    #
    @12
    cN
    cn0
    wcel
    @5
    cn0
    wcel
    @51
    cN
    peano2nn0
    syl
    #
    expp1d
    @12
    @6
    c2
    @12
    @6
    @12
    c2
    @5
    @45
    @12
    2nn0
    a1i
    @53
    nn0expcld
    nn0cnd
    #
    @52
    mulcomd
    3eqtrd
    adantr
    oveq2d
    @48
    @32
    c2
    @6
    @38
    @32
    cc
    wcel
    @12
    @32
    nn0cn
    adantl
    @48
    2cnd
    @12
    @6
    cc
    wcel
    @38
    @54
    adantr
    mulassd
    eqtr4d
    3ad2antl1
    adantr
    oveq1d
    rspcedvd
    ex
    rexlimdva
    mpd
    3exp
    jaoi
    sylbi
    3imp
end
