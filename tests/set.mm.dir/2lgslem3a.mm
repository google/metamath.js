include "c8.mm"
include "cmul.mm"
include "co.mm"
include "c1.mm"
include "caddc.mm"
include "wceq.mm"
include "cn0.mm"
include "wcel.mm"
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
include "cc.mm"
include "8nn0.mm"
include "a1i.mm"
include "id.mm"
include "nn0mulcld.mm"
include "nn0cnd.mm"
include "pncan1.mm"
include "syl.mm"
include "4cn.mm"
include "2cn.mm"
include "4t2e8.mm"
include "mulcomli.mm"
include "eqcomi.mm"
include "nn0cn.mm"
include "mulassd.mm"
include "eqtrd.mm"
include "4nn0.mm"
include "cc0.mm"
include "wne.mm"
include "2ne0.mm"
include "divcan3d.mm"
include "3eqtrd.mm"
include "wa.mm"
include "1cnd.mm"
include "4ne0.mm"
include "pm3.2i.mm"
include "divdir.mm"
include "syl3anc.mm"
include "8cn.mm"
include "div23.mm"
include "oveq1i.mm"
include "divcan3i.mm"
include "eqtri.mm"
include "clt.mm"
include "wbr.mm"
include "1lt4.mm"
include "cz.mm"
include "cn.mm"
include "wb.mm"
include "2nn0.mm"
include "nn0zd.mm"
include "1nn0.mm"
include "4nn.mm"
include "adddivflid.mm"
include "mpbii.mm"
include "2t2e4.mm"
include "2txmxeqx.mm"
include "sylan9eqr.mm"

theorem 2lgslem3a
  let cP: class P
  let cK: class K
  let cN: class N
  assume 2lgslem2.n: |- N = ( ( ( P - 1 ) / 2 ) - ( |_ ` ( P / 4 ) ) )


  assert |- ( ( K e. NN0 /\ P = ( ( 8 x. K ) + 1 ) ) -> N = ( 2 x. K ) )

  proof
    cP
    c8
    cK
    cmul
    co
    #
    c1
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
    @11
    @5
    @13
    @7
    cmin
    @2
    @10
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
    @12
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
    @9
    cmin
    co
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
    @5
    @14
    @7
    @9
    cmin
    @3
    @5
    @0
    c2
    cdiv
    co
    c2
    @14
    cmul
    co
    #
    c2
    cdiv
    co
    @14
    @3
    @4
    @0
    c2
    cdiv
    @3
    @0
    cc
    wcel
    #
    @4
    @0
    wceq
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
    @0
    pncan1
    syl
    oveq1d
    @3
    @0
    @17
    c2
    cdiv
    @3
    @0
    c2
    c4
    cmul
    co
    #
    cK
    cmul
    co
    @17
    @3
    c8
    @21
    cK
    cmul
    c8
    @21
    wceq
    @3
    @21
    c8
    c4
    c2
    c8
    4cn
    2cn
    4t2e8
    mulcomli
    eqcomi
    a1i
    oveq1d
    @3
    c2
    c4
    cK
    c2
    cc
    wcel
    @3
    2cn
    a1i
    #
    c4
    cc
    wcel
    #
    @3
    4cn
    a1i
    cK
    nn0cn
    #
    mulassd
    eqtrd
    oveq1d
    @3
    @14
    c2
    @3
    @14
    @3
    c4
    cK
    c4
    cn0
    wcel
    @3
    4nn0
    a1i
    @19
    nn0mulcld
    nn0cnd
    @22
    c2
    cc0
    wne
    @3
    2ne0
    a1i
    divcan3d
    3eqtrd
    @3
    @7
    @9
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
    @9
    @3
    @6
    @26
    cfl
    @3
    @6
    @0
    c4
    cdiv
    co
    #
    @25
    caddc
    co
    #
    @26
    @3
    @18
    c1
    cc
    wcel
    @23
    c4
    cc0
    wne
    #
    wa
    #
    @6
    @29
    wceq
    @20
    @3
    1cnd
    @31
    @3
    @23
    @30
    4cn
    4ne0
    pm3.2i
    a1i
    #
    @0
    c1
    c4
    divdir
    syl3anc
    @3
    @28
    @9
    @25
    caddc
    @3
    @28
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
    @31
    @28
    @34
    wceq
    @35
    @3
    8cn
    a1i
    @24
    @32
    c8
    cK
    c4
    div23
    syl3anc
    @3
    @33
    c2
    cK
    cmul
    @33
    c2
    wceq
    @3
    @33
    c4
    c2
    cmul
    co
    #
    c4
    cdiv
    co
    c2
    c8
    @36
    c4
    cdiv
    @36
    c8
    4t2e8
    eqcomi
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
    @27
    @9
    wceq
    #
    1lt4
    @3
    @9
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
    @37
    @38
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
    @19
    nn0mulcld
    #
    nn0zd
    @39
    @3
    1nn0
    a1i
    @40
    @3
    4nn
    a1i
    @9
    c1
    c4
    adddivflid
    syl3anc
    mpbii
    eqtrd
    oveq12d
    @3
    @14
    @15
    @9
    cmin
    @3
    @14
    c2
    c2
    cmul
    co
    #
    cK
    cmul
    co
    @15
    @3
    c4
    @42
    cK
    cmul
    c4
    @42
    wceq
    @3
    @42
    c4
    2t2e4
    eqcomi
    a1i
    oveq1d
    @3
    c2
    c2
    cK
    @22
    @22
    @24
    mulassd
    eqtrd
    oveq1d
    @3
    @9
    cc
    wcel
    @16
    @9
    wceq
    @3
    @9
    @41
    nn0cnd
    @9
    2txmxeqx
    syl
    3eqtrd
    sylan9eqr
end
