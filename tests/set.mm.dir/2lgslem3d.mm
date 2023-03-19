include "c8.mm"
include "cmul.mm"
include "co.mm"
include "c7.mm"
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
include "c3.mm"
include "c6.mm"
include "8nn0.mm"
include "a1i.mm"
include "id.mm"
include "nn0mulcld.mm"
include "nn0cnd.mm"
include "cc.mm"
include "7cn.mm"
include "1cnd.mm"
include "addsubassd.mm"
include "4t2e8.mm"
include "eqcomi.mm"
include "4cn.mm"
include "2cn.mm"
include "nn0cn.mm"
include "mul32d.mm"
include "eqtrd.mm"
include "df-7.mm"
include "oveq1i.mm"
include "6cn.mm"
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
include "3t2e6.mm"
include "3cn.mm"
include "divcan4i.mm"
include "3eqtrd.mm"
include "4ne0.mm"
include "pm3.2i.mm"
include "8cn.mm"
include "div23.mm"
include "divcan3i.mm"
include "clt.mm"
include "wbr.mm"
include "3lt4.mm"
include "cz.mm"
include "cn.mm"
include "wb.mm"
include "2nn0.mm"
include "nn0zd.mm"
include "peano2zd.mm"
include "3nn0.mm"
include "4nn.mm"
include "adddivflid.mm"
include "divcld.mm"
include "addassd.mm"
include "4p3e7.mm"
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
include "3m1e2.mm"
include "sylan9eqr.mm"

theorem 2lgslem3d
  let cP: class P
  let cK: class K
  let cN: class N
  assume 2lgslem2.n: |- N = ( ( ( P - 1 ) / 2 ) - ( |_ ` ( P / 4 ) ) )


  assert |- ( ( K e. NN0 /\ P = ( ( 8 x. K ) + 7 ) ) -> N = ( ( 2 x. K ) + 2 ) )

  proof
    cP
    c8
    cK
    cmul
    co
    #
    c7
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
    c2
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
    c3
    caddc
    co
    #
    @9
    c1
    caddc
    co
    #
    cmin
    co
    @15
    @9
    cmin
    co
    #
    c3
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
    @17
    cmin
    @3
    @5
    @15
    c2
    cmul
    co
    #
    c6
    caddc
    co
    #
    c2
    cdiv
    co
    #
    @20
    c2
    cdiv
    co
    #
    c6
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
    @21
    c2
    cdiv
    @3
    @4
    @0
    c7
    c1
    cmin
    co
    #
    caddc
    co
    @21
    @3
    @0
    c7
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
    c7
    cc
    wcel
    #
    @3
    7cn
    a1i
    #
    @3
    1cnd
    #
    addsubassd
    @3
    @0
    @20
    @26
    c6
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
    @20
    @3
    c8
    @32
    cK
    cmul
    c8
    @32
    wceq
    @3
    @32
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
    @26
    c6
    wceq
    @3
    @26
    c6
    c1
    caddc
    co
    #
    c1
    cmin
    co
    #
    c6
    c7
    @39
    c1
    cmin
    df-7
    oveq1i
    c6
    cc
    wcel
    #
    @40
    c6
    wceq
    6cn
    c6
    pncan1
    ax-mp
    eqtri
    a1i
    oveq12d
    eqtrd
    oveq1d
    @3
    @20
    cc
    wcel
    @41
    @36
    c2
    cc0
    wne
    #
    wa
    @22
    @25
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
    @27
    nn0mulcld
    nn0cnd
    #
    @37
    mulcld
    @41
    @3
    6cn
    a1i
    @3
    c2
    c2
    crp
    wcel
    @3
    2rp
    a1i
    rpcnne0d
    @20
    c6
    c2
    divdir
    syl3anc
    @3
    @23
    @15
    @24
    c3
    caddc
    @3
    @15
    c2
    @43
    @37
    @42
    @3
    2ne0
    a1i
    divcan4d
    @24
    c3
    wceq
    @3
    @24
    c3
    c2
    cmul
    co
    #
    c2
    cdiv
    co
    c3
    c6
    @44
    c2
    cdiv
    @44
    c6
    3t2e6
    eqcomi
    oveq1i
    c3
    c2
    3cn
    2cn
    2ne0
    divcan4i
    eqtri
    a1i
    oveq12d
    3eqtrd
    @3
    @7
    @9
    c7
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
    @17
    @3
    @6
    @46
    cfl
    @3
    @6
    @0
    c4
    cdiv
    co
    #
    @45
    caddc
    co
    #
    @46
    @3
    @0
    cc
    wcel
    @29
    @34
    c4
    cc0
    wne
    #
    wa
    #
    @6
    @49
    wceq
    @28
    @30
    @51
    @3
    @34
    @50
    4cn
    4ne0
    pm3.2i
    a1i
    #
    @0
    c7
    c4
    divdir
    syl3anc
    @3
    @48
    @9
    @45
    caddc
    @3
    @48
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
    @51
    @48
    @54
    wceq
    @55
    @3
    8cn
    a1i
    @38
    @52
    c8
    cK
    c4
    div23
    syl3anc
    @3
    @53
    c2
    cK
    cmul
    @53
    c2
    wceq
    @3
    @53
    @32
    c4
    cdiv
    co
    c2
    c8
    @32
    c4
    cdiv
    @33
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
    c3
    c4
    clt
    wbr
    #
    @47
    @17
    wceq
    #
    3lt4
    @3
    @56
    @17
    c3
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
    @17
    wceq
    #
    @57
    @3
    @17
    cz
    wcel
    c3
    cn0
    wcel
    #
    c4
    cn
    wcel
    #
    @56
    @61
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
    @27
    nn0mulcld
    #
    nn0zd
    peano2zd
    @62
    @3
    3nn0
    a1i
    @63
    @3
    4nn
    a1i
    @17
    c3
    c4
    adddivflid
    syl3anc
    @3
    @60
    @47
    @17
    @3
    @59
    @46
    cfl
    @3
    @59
    @9
    c1
    @58
    caddc
    co
    #
    caddc
    co
    @46
    @3
    @9
    c1
    @58
    @3
    c2
    cK
    @37
    @38
    mulcld
    @31
    @3
    c3
    c4
    c3
    cc
    wcel
    @3
    3cn
    a1i
    #
    @35
    @50
    @3
    4ne0
    a1i
    divcld
    addassd
    @3
    @65
    @45
    @9
    caddc
    @3
    @45
    @65
    @45
    @65
    wceq
    @3
    @45
    c4
    c3
    caddc
    co
    #
    c4
    cdiv
    co
    c4
    c4
    cdiv
    co
    #
    @58
    caddc
    co
    @65
    c7
    @67
    c4
    cdiv
    @67
    c7
    4p3e7
    eqcomi
    oveq1i
    c4
    c3
    c4
    4cn
    3cn
    4cn
    4ne0
    divdiri
    @68
    c1
    @58
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
    c3
    @9
    c1
    @43
    @66
    @3
    @9
    @64
    nn0cnd
    #
    @31
    addsub4d
    @3
    @18
    @9
    @19
    c2
    caddc
    @3
    @18
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
    @70
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
    @70
    @3
    c4
    @72
    cK
    cmul
    c4
    @72
    wceq
    @3
    @72
    c4
    2t2e4
    eqcomi
    a1i
    oveq1d
    @3
    c2
    c2
    cK
    @37
    @37
    @38
    mulassd
    eqtrd
    oveq1d
    @3
    @9
    cc
    wcel
    @71
    @9
    wceq
    @69
    @9
    2txmxeqx
    syl
    eqtrd
    @19
    c2
    wceq
    @3
    3m1e2
    a1i
    oveq12d
    3eqtrd
    sylan9eqr
end
