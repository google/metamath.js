include "cc.mm"
include "wcel.mm"
include "wa.mm"
include "ccos.mm"
include "cfv.mm"
include "cc0.mm"
include "wne.mm"
include "caddc.mm"
include "co.mm"
include "w3a.mm"
include "ctan.mm"
include "csin.mm"
include "cdiv.mm"
include "c1.mm"
include "cmul.mm"
include "cmin.mm"
include "wceq.mm"
include "addcl.mm"
include "adantr.mm"
include "simpr3.mm"
include "tanval.mm"
include "syl2anc.mm"
include "sinadd.mm"
include "cosadd.mm"
include "oveq12d.mm"
include "simpll.mm"
include "coscld.mm"
include "simplr.mm"
include "mulcld.mm"
include "simpr1.mm"
include "tancld.mm"
include "simpr2.mm"
include "adddid.mm"
include "mul32d.mm"
include "oveq2d.mm"
include "sincld.mm"
include "divcan2d.mm"
include "eqtrd.mm"
include "oveq1d.mm"
include "mulassd.mm"
include "1cnd.mm"
include "subdid.mm"
include "mulid1d.mm"
include "mul4d.mm"
include "addcld.mm"
include "ax-1cn.mm"
include "subcl.mm"
include "sylancr.mm"
include "wb.mm"
include "tanaddlem.mm"
include "3adantr3.mm"
include "mpbid.mm"
include "necomd.mm"
include "subeq0.mm"
include "necon3bid.mm"
include "mpbird.mm"
include "mulne0d.mm"
include "divcan5d.mm"
include "3eqtr2rd.mm"
include "eqtr4d.mm"

theorem tanadd
  let cA: class A
  let cB: class B


  assert |- ( ( ( A e. CC /\ B e. CC ) /\ ( ( cos ` A ) =/= 0 /\ ( cos ` B ) =/= 0 /\ ( cos ` ( A + B ) ) =/= 0 ) ) -> ( tan ` ( A + B ) ) = ( ( ( tan ` A ) + ( tan ` B ) ) / ( 1 - ( ( tan ` A ) x. ( tan ` B ) ) ) ) )

  proof
    cA
    cc
    wcel
    #
    cB
    cc
    wcel
    #
    wa
    #
    cA
    ccos
    cfv
    #
    cc0
    wne
    #
    cB
    ccos
    cfv
    #
    cc0
    wne
    #
    cA
    cB
    caddc
    co
    #
    ccos
    cfv
    #
    cc0
    wne
    #
    w3a
    #
    wa
    #
    @7
    ctan
    cfv
    #
    @7
    csin
    cfv
    #
    @8
    cdiv
    co
    #
    cA
    ctan
    cfv
    #
    cB
    ctan
    cfv
    #
    caddc
    co
    #
    c1
    @15
    @16
    cmul
    co
    #
    cmin
    co
    #
    cdiv
    co
    #
    @11
    @7
    cc
    wcel
    #
    @9
    @12
    @14
    wceq
    @2
    @21
    @10
    cA
    cB
    addcl
    adantr
    @2
    @4
    @6
    @9
    simpr3
    #
    @7
    tanval
    syl2anc
    @11
    @14
    cA
    csin
    cfv
    #
    @5
    cmul
    co
    #
    @3
    cB
    csin
    cfv
    #
    cmul
    co
    #
    caddc
    co
    #
    @3
    @5
    cmul
    co
    #
    @23
    @25
    cmul
    co
    #
    cmin
    co
    #
    cdiv
    co
    @28
    @17
    cmul
    co
    #
    @28
    @19
    cmul
    co
    #
    cdiv
    co
    @20
    @11
    @13
    @27
    @8
    @30
    cdiv
    @2
    @13
    @27
    wceq
    @10
    cA
    cB
    sinadd
    adantr
    @2
    @8
    @30
    wceq
    @10
    cA
    cB
    cosadd
    adantr
    oveq12d
    @11
    @31
    @27
    @32
    @30
    cdiv
    @11
    @31
    @28
    @15
    cmul
    co
    #
    @28
    @16
    cmul
    co
    #
    caddc
    co
    @27
    @11
    @28
    @15
    @16
    @11
    @3
    @5
    @11
    cA
    @0
    @1
    @10
    simpll
    #
    coscld
    #
    @11
    cB
    @0
    @1
    @10
    simplr
    #
    coscld
    #
    mulcld
    #
    @11
    cA
    @35
    @2
    @4
    @6
    @9
    simpr1
    #
    tancld
    #
    @11
    cB
    @37
    @2
    @4
    @6
    @9
    simpr2
    #
    tancld
    #
    adddid
    @11
    @33
    @24
    @34
    @26
    caddc
    @11
    @33
    @3
    @15
    cmul
    co
    #
    @5
    cmul
    co
    @24
    @11
    @3
    @5
    @15
    @36
    @38
    @41
    mul32d
    @11
    @44
    @23
    @5
    cmul
    @11
    @44
    @3
    @23
    @3
    cdiv
    co
    #
    cmul
    co
    @23
    @11
    @15
    @45
    @3
    cmul
    @11
    @0
    @4
    @15
    @45
    wceq
    @35
    @40
    cA
    tanval
    syl2anc
    oveq2d
    @11
    @23
    @3
    @11
    cA
    @35
    sincld
    @36
    @40
    divcan2d
    eqtrd
    #
    oveq1d
    eqtrd
    @11
    @34
    @3
    @5
    @16
    cmul
    co
    #
    cmul
    co
    @26
    @11
    @3
    @5
    @16
    @36
    @38
    @43
    mulassd
    @11
    @47
    @25
    @3
    cmul
    @11
    @47
    @5
    @25
    @5
    cdiv
    co
    #
    cmul
    co
    @25
    @11
    @16
    @48
    @5
    cmul
    @11
    @1
    @6
    @16
    @48
    wceq
    @37
    @42
    cB
    tanval
    syl2anc
    oveq2d
    @11
    @25
    @5
    @11
    cB
    @37
    sincld
    @38
    @42
    divcan2d
    eqtrd
    #
    oveq2d
    eqtrd
    oveq12d
    eqtrd
    @11
    @32
    @28
    c1
    cmul
    co
    #
    @28
    @18
    cmul
    co
    #
    cmin
    co
    @30
    @11
    @28
    c1
    @18
    @39
    @11
    1cnd
    @11
    @15
    @16
    @41
    @43
    mulcld
    #
    subdid
    @11
    @50
    @28
    @51
    @29
    cmin
    @11
    @28
    @39
    mulid1d
    @11
    @51
    @44
    @47
    cmul
    co
    @29
    @11
    @3
    @5
    @15
    @16
    @36
    @38
    @41
    @43
    mul4d
    @11
    @44
    @23
    @47
    @25
    cmul
    @46
    @49
    oveq12d
    eqtrd
    oveq12d
    eqtrd
    oveq12d
    @11
    @17
    @19
    @28
    @11
    @15
    @16
    @41
    @43
    addcld
    @11
    c1
    cc
    wcel
    #
    @18
    cc
    wcel
    #
    @19
    cc
    wcel
    ax-1cn
    @52
    c1
    @18
    subcl
    sylancr
    @39
    @11
    @19
    cc0
    wne
    #
    c1
    @18
    wne
    #
    @11
    @18
    c1
    @11
    @9
    @18
    c1
    wne
    #
    @22
    @2
    @4
    @6
    @9
    @57
    wb
    @9
    cA
    cB
    tanaddlem
    3adantr3
    mpbid
    necomd
    @11
    @53
    @54
    @55
    @56
    wb
    ax-1cn
    @52
    @53
    @54
    wa
    @19
    cc0
    c1
    @18
    c1
    @18
    subeq0
    necon3bid
    sylancr
    mpbird
    @11
    @3
    @5
    @36
    @38
    @40
    @42
    mulne0d
    divcan5d
    3eqtr2rd
    eqtr4d
end
