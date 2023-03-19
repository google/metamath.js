include "c8.mm"
include "cmul.mm"
include "co.mm"
include "c3.mm"
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
include "3cn.mm"
include "1cnd.mm"
include "addsubassd.mm"
include "4t2e8.mm"
include "eqcomi.mm"
include "4cn.mm"
include "2cn.mm"
include "nn0cn.mm"
include "mul32d.mm"
include "eqtrd.mm"
include "3m1e2.mm"
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
include "2div2e1.mm"
include "3eqtrd.mm"
include "4ne0.mm"
include "pm3.2i.mm"
include "8cn.mm"
include "div23.mm"
include "oveq1i.mm"
include "divcan3i.mm"
include "eqtri.mm"
include "clt.mm"
include "wbr.mm"
include "3lt4.mm"
include "cz.mm"
include "cn.mm"
include "wb.mm"
include "2nn0.mm"
include "nn0zd.mm"
include "3nn0.mm"
include "4nn.mm"
include "adddivflid.mm"
include "mpbii.mm"
include "addsubd.mm"
include "2t2e4.mm"
include "mulassd.mm"
include "2txmxeqx.mm"
include "syl.mm"
include "sylan9eqr.mm"

theorem 2lgslem3b
  let cP: class P
  let cK: class K
  let cN: class N
  assume 2lgslem2.n: |- N = ( ( ( P - 1 ) / 2 ) - ( |_ ` ( P / 4 ) ) )


  assert |- ( ( K e. NN0 /\ P = ( ( 8 x. K ) + 3 ) ) -> N = ( ( 2 x. K ) + 1 ) )

  proof
    cP
    c8
    cK
    cmul
    co
    #
    c3
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
    c1
    caddc
    co
    #
    @9
    cmin
    co
    @15
    @9
    cmin
    co
    #
    c1
    caddc
    co
    @10
    @3
    @5
    @16
    @7
    @9
    cmin
    @3
    @5
    @15
    c2
    cmul
    co
    #
    c2
    caddc
    co
    #
    c2
    cdiv
    co
    #
    @18
    c2
    cdiv
    co
    #
    c2
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
    @19
    c2
    cdiv
    @3
    @4
    @0
    c3
    c1
    cmin
    co
    #
    caddc
    co
    @19
    @3
    @0
    c3
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
    c3
    cc
    wcel
    #
    @3
    3cn
    a1i
    #
    @3
    1cnd
    #
    addsubassd
    @3
    @0
    @18
    @24
    c2
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
    @18
    @3
    c8
    @30
    cK
    cmul
    c8
    @30
    wceq
    @3
    @30
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
    @24
    c2
    wceq
    @3
    3m1e2
    a1i
    oveq12d
    eqtrd
    oveq1d
    @3
    @18
    cc
    wcel
    @33
    @33
    c2
    cc0
    wne
    #
    wa
    @20
    @23
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
    @25
    nn0mulcld
    nn0cnd
    #
    @34
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
    @18
    c2
    c2
    divdir
    syl3anc
    @3
    @21
    @15
    @22
    c1
    caddc
    @3
    @15
    c2
    @37
    @34
    @36
    @3
    2ne0
    a1i
    divcan4d
    @22
    c1
    wceq
    @3
    2div2e1
    a1i
    oveq12d
    3eqtrd
    @3
    @7
    @9
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
    @9
    @3
    @6
    @39
    cfl
    @3
    @6
    @0
    c4
    cdiv
    co
    #
    @38
    caddc
    co
    #
    @39
    @3
    @0
    cc
    wcel
    @27
    @32
    c4
    cc0
    wne
    #
    wa
    #
    @6
    @42
    wceq
    @26
    @28
    @44
    @3
    @32
    @43
    4cn
    4ne0
    pm3.2i
    a1i
    #
    @0
    c3
    c4
    divdir
    syl3anc
    @3
    @41
    @9
    @38
    caddc
    @3
    @41
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
    @44
    @41
    @47
    wceq
    @48
    @3
    8cn
    a1i
    @35
    @45
    c8
    cK
    c4
    div23
    syl3anc
    @3
    @46
    c2
    cK
    cmul
    @46
    c2
    wceq
    @3
    @46
    @30
    c4
    cdiv
    co
    c2
    c8
    @30
    c4
    cdiv
    @31
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
    @40
    @9
    wceq
    #
    3lt4
    @3
    @9
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
    @49
    @50
    wb
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
    @25
    nn0mulcld
    #
    nn0zd
    @51
    @3
    3nn0
    a1i
    @52
    @3
    4nn
    a1i
    @9
    c3
    c4
    adddivflid
    syl3anc
    mpbii
    eqtrd
    oveq12d
    @3
    @15
    c1
    @9
    @37
    @29
    @3
    @9
    @53
    nn0cnd
    #
    addsubd
    @3
    @17
    @9
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
    @55
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
    @55
    @3
    c4
    @57
    cK
    cmul
    c4
    @57
    wceq
    @3
    @57
    c4
    2t2e4
    eqcomi
    a1i
    oveq1d
    @3
    c2
    c2
    cK
    @34
    @34
    @35
    mulassd
    eqtrd
    oveq1d
    @3
    @9
    cc
    wcel
    @56
    @9
    wceq
    @54
    @9
    2txmxeqx
    syl
    eqtrd
    oveq1d
    3eqtrd
    sylan9eqr
end
