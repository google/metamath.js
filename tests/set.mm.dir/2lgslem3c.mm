include "c8.mm"
include "cmul.mm"
include "co.mm"
include "c5.mm"
include "caddc.mm"
include "wceq.mm"
include "cn0.mm"
include "wcel.mm"
include "c1.mm"
include "cmin.mm"
include "c2.mm"
include "cdiv.mm"
include "c4.mm"
include "cfl.mm"
include "cfv.mm"
include "oveq1.mm"
include "oveq1d.mm"
include "fveq2d.mm"
include "oveq12d.mm"
include "syl5eq.mm"
include "8nn0.mm"
include "a1i.mm"
include "id.mm"
include "nn0mulcld.mm"
include "nn0cnd.mm"
include "cc.mm"
include "5cn.mm"
include "1cnd.mm"
include "addsubassd.mm"
include "4t2e8.mm"
include "eqcomi.mm"
include "4cn.mm"
include "2cn.mm"
include "nn0cn.mm"
include "mul32d.mm"
include "eqtrd.mm"
include "df-5.mm"
include "oveq1i.mm"
include "pncan1.mm"
include "ax-mp.mm"
include "eqtri.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "4nn0.mm"
include "mulcld.mm"
include "crp.mm"
include "2rp.mm"
include "rpcnne0d.mm"
include "divdir.mm"
include "syl3anc.mm"
include "2ne0.mm"
include "divcan4d.mm"
include "4d2e2.mm"
include "3eqtrd.mm"
include "4ne0.mm"
include "pm3.2i.mm"
include "8cn.mm"
include "div23.mm"
include "divcan3i.mm"
include "clt.mm"
include "wbr.mm"
include "1lt4.mm"
include "cz.mm"
include "cn.mm"
include "wb.mm"
include "2nn0.mm"
include "nn0zd.mm"
include "peano2zd.mm"
include "1nn0.mm"
include "4nn.mm"
include "adddivflid.mm"
include "reccld.mm"
include "addassd.mm"
include "ax-1cn.mm"
include "divdiri.mm"
include "dividi.mm"
include "3eqtri.mm"
include "eqcomd.mm"
include "oveq2d.mm"
include "eqeq1d.mm"
include "bitrd.mm"
include "mpbii.mm"
include "addsub4d.mm"
include "2t2e4.mm"
include "mulassd.mm"
include "2txmxeqx.mm"
include "syl.mm"
include "2m1e1.mm"
include "sylan9eqr.mm"

theorem 2lgslem3c
  let cP: class P
  let cK: class K
  let cN: class N
  assume 2lgslem2.n: |- N = ( ( ( P - 1 ) / 2 ) - ( |_ ` ( P / 4 ) ) )


  assert |- ( ( K e. NN0 /\ P = ( ( 8 x. K ) + 5 ) ) -> N = ( ( 2 x. K ) + 1 ) )

  proof
    cP
    c8
    cK
    cmul
    co
    #
    c5
    caddc
    co
    #
    wceq
    #
    cK
    cn0
    wcel
    #
    cN
    @1
    c1
    cmin
    co
    #
    c2
    cdiv
    co
    #
    @1
    c4
    cdiv
    co
    #
    cfl
    cfv
    #
    cmin
    co
    #
    c2
    cK
    cmul
    co
    #
    c1
    caddc
    co
    #
    @2
    cN
    cP
    c1
    cmin
    co
    #
    c2
    cdiv
    co
    #
    cP
    c4
    cdiv
    co
    #
    cfl
    cfv
    #
    cmin
    co
    @8
    2lgslem2.n
    @2
    @12
    @5
    @14
    @7
    cmin
    @2
    @11
    @4
    c2
    cdiv
    cP
    @1
    c1
    cmin
    oveq1
    oveq1d
    @2
    @13
    @6
    cfl
    cP
    @1
    c4
    cdiv
    oveq1
    fveq2d
    oveq12d
    syl5eq
    @3
    @8
    c4
    cK
    cmul
    co
    #
    c2
    caddc
    co
    #
    @10
    cmin
    co
    @15
    @9
    cmin
    co
    #
    c2
    c1
    cmin
    co
    #
    caddc
    co
    @10
    @3
    @5
    @16
    @7
    @10
    cmin
    @3
    @5
    @15
    c2
    cmul
    co
    #
    c4
    caddc
    co
    #
    c2
    cdiv
    co
    #
    @19
    c2
    cdiv
    co
    #
    c4
    c2
    cdiv
    co
    #
    caddc
    co
    #
    @16
    @3
    @4
    @20
    c2
    cdiv
    @3
    @4
    @0
    c5
    c1
    cmin
    co
    #
    caddc
    co
    @20
    @3
    @0
    c5
    c1
    @3
    @0
    @3
    c8
    cK
    c8
    cn0
    wcel
    @3
    8nn0
    a1i
    @3
    id
    #
    nn0mulcld
    nn0cnd
    #
    c5
    cc
    wcel
    #
    @3
    5cn
    a1i
    #
    @3
    1cnd
    #
    addsubassd
    @3
    @0
    @19
    @25
    c4
    caddc
    @3
    @0
    c4
    c2
    cmul
    co
    #
    cK
    cmul
    co
    @19
    @3
    c8
    @31
    cK
    cmul
    c8
    @31
    wceq
    @3
    @31
    c8
    4t2e8
    eqcomi
    #
    a1i
    oveq1d
    @3
    c4
    c2
    cK
    c4
    cc
    wcel
    #
    @3
    4cn
    a1i
    #
    c2
    cc
    wcel
    #
    @3
    2cn
    a1i
    #
    cK
    nn0cn
    #
    mul32d
    eqtrd
    @25
    c4
    wceq
    @3
    @25
    c4
    c1
    caddc
    co
    #
    c1
    cmin
    co
    #
    c4
    c5
    @38
    c1
    cmin
    df-5
    oveq1i
    @33
    @39
    c4
    wceq
    4cn
    c4
    pncan1
    ax-mp
    eqtri
    a1i
    oveq12d
    eqtrd
    oveq1d
    @3
    @19
    cc
    wcel
    @33
    @35
    c2
    cc0
    wne
    #
    wa
    @21
    @24
    wceq
    @3
    @15
    c2
    @3
    @15
    @3
    c4
    cK
    c4
    cn0
    wcel
    @3
    4nn0
    a1i
    @26
    nn0mulcld
    nn0cnd
    #
    @36
    mulcld
    @34
    @3
    c2
    c2
    crp
    wcel
    @3
    2rp
    a1i
    rpcnne0d
    @19
    c4
    c2
    divdir
    syl3anc
    @3
    @22
    @15
    @23
    c2
    caddc
    @3
    @15
    c2
    @41
    @36
    @40
    @3
    2ne0
    a1i
    divcan4d
    @23
    c2
    wceq
    @3
    4d2e2
    a1i
    oveq12d
    3eqtrd
    @3
    @7
    @9
    c5
    c4
    cdiv
    co
    #
    caddc
    co
    #
    cfl
    cfv
    #
    @10
    @3
    @6
    @43
    cfl
    @3
    @6
    @0
    c4
    cdiv
    co
    #
    @42
    caddc
    co
    #
    @43
    @3
    @0
    cc
    wcel
    @28
    @33
    c4
    cc0
    wne
    #
    wa
    #
    @6
    @46
    wceq
    @27
    @29
    @48
    @3
    @33
    @47
    4cn
    4ne0
    pm3.2i
    a1i
    #
    @0
    c5
    c4
    divdir
    syl3anc
    @3
    @45
    @9
    @42
    caddc
    @3
    @45
    c8
    c4
    cdiv
    co
    #
    cK
    cmul
    co
    #
    @9
    @3
    c8
    cc
    wcel
    #
    cK
    cc
    wcel
    @48
    @45
    @51
    wceq
    @52
    @3
    8cn
    a1i
    @37
    @49
    c8
    cK
    c4
    div23
    syl3anc
    @3
    @50
    c2
    cK
    cmul
    @50
    c2
    wceq
    @3
    @50
    @31
    c4
    cdiv
    co
    c2
    c8
    @31
    c4
    cdiv
    @32
    oveq1i
    c2
    c4
    2cn
    4cn
    4ne0
    divcan3i
    eqtri
    a1i
    oveq1d
    eqtrd
    oveq1d
    eqtrd
    fveq2d
    @3
    c1
    c4
    clt
    wbr
    #
    @44
    @10
    wceq
    #
    1lt4
    @3
    @53
    @10
    c1
    c4
    cdiv
    co
    #
    caddc
    co
    #
    cfl
    cfv
    #
    @10
    wceq
    #
    @54
    @3
    @10
    cz
    wcel
    c1
    cn0
    wcel
    #
    c4
    cn
    wcel
    #
    @53
    @58
    wb
    @3
    @9
    @3
    @9
    @3
    c2
    cK
    c2
    cn0
    wcel
    @3
    2nn0
    a1i
    @26
    nn0mulcld
    #
    nn0zd
    peano2zd
    @59
    @3
    1nn0
    a1i
    @60
    @3
    4nn
    a1i
    @10
    c1
    c4
    adddivflid
    syl3anc
    @3
    @57
    @44
    @10
    @3
    @56
    @43
    cfl
    @3
    @56
    @9
    c1
    @55
    caddc
    co
    #
    caddc
    co
    @43
    @3
    @9
    c1
    @55
    @3
    c2
    cK
    @36
    @37
    mulcld
    @30
    @3
    c4
    @34
    @47
    @3
    4ne0
    a1i
    reccld
    addassd
    @3
    @62
    @42
    @9
    caddc
    @3
    @42
    @62
    @42
    @62
    wceq
    @3
    @42
    @38
    c4
    cdiv
    co
    c4
    c4
    cdiv
    co
    #
    @55
    caddc
    co
    @62
    c5
    @38
    c4
    cdiv
    df-5
    oveq1i
    c4
    c1
    c4
    4cn
    ax-1cn
    4cn
    4ne0
    divdiri
    @63
    c1
    @55
    caddc
    c4
    4cn
    4ne0
    dividi
    oveq1i
    3eqtri
    a1i
    eqcomd
    oveq2d
    eqtrd
    fveq2d
    eqeq1d
    bitrd
    mpbii
    eqtrd
    oveq12d
    @3
    @15
    c2
    @9
    c1
    @41
    @36
    @3
    @9
    @61
    nn0cnd
    #
    @30
    addsub4d
    @3
    @17
    @9
    @18
    c1
    caddc
    @3
    @17
    c2
    @9
    cmul
    co
    #
    @9
    cmin
    co
    #
    @9
    @3
    @15
    @65
    @9
    cmin
    @3
    @15
    c2
    c2
    cmul
    co
    #
    cK
    cmul
    co
    @65
    @3
    c4
    @67
    cK
    cmul
    c4
    @67
    wceq
    @3
    @67
    c4
    2t2e4
    eqcomi
    a1i
    oveq1d
    @3
    c2
    c2
    cK
    @36
    @36
    @37
    mulassd
    eqtrd
    oveq1d
    @3
    @9
    cc
    wcel
    @66
    @9
    wceq
    @64
    @9
    2txmxeqx
    syl
    eqtrd
    @18
    c1
    wceq
    @3
    2m1e1
    a1i
    oveq12d
    3eqtrd
    sylan9eqr
end
