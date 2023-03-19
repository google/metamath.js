include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "cz.mm"
include "crp.mm"
include "cmo.mm"
include "co.mm"
include "wceq.mm"
include "cmul.mm"
include "cdiv.mm"
include "cfl.mm"
include "cfv.mm"
include "cmin.mm"
include "wb.mm"
include "modval.mm"
include "eqeqan12d.mm"
include "anandirs.mm"
include "adantrl.mm"
include "oveq1.mm"
include "syl6bi.mm"
include "cc.mm"
include "rpcn.mm"
include "ad2antll.mm"
include "zcn.mm"
include "ad2antrl.mm"
include "rerpdivcl.mm"
include "flcld.mm"
include "zcnd.mm"
include "mulassd.mm"
include "mul32d.mm"
include "eqtr3d.mm"
include "oveq2d.mm"
include "recn.mm"
include "adantr.mm"
include "adantl.mm"
include "mulcld.mm"
include "subdird.mm"
include "eqtr4d.mm"
include "adantlr.mm"
include "adantll.mm"
include "eqeq12d.mm"
include "sylibrd.mm"
include "zre.mm"
include "remulcl.mm"
include "sylan2.mm"
include "adantrr.mm"
include "simprr.mm"
include "simprl.mm"
include "zmulcld.mm"
include "modcyc2.mm"
include "syl3anc.mm"
include "syl5ib.mm"
include "syld.mm"
include "3impia.mm"

theorem modmul1
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- ( ( ( A e. RR /\ B e. RR ) /\ ( C e. ZZ /\ D e. RR+ ) /\ ( A mod D ) = ( B mod D ) ) -> ( ( A x. C ) mod D ) = ( ( B x. C ) mod D ) )

  proof
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    wa
    #
    cC
    cz
    wcel
    #
    cD
    crp
    wcel
    #
    wa
    #
    cA
    cD
    cmo
    co
    #
    cB
    cD
    cmo
    co
    #
    wceq
    #
    cA
    cC
    cmul
    co
    #
    cD
    cmo
    co
    #
    cB
    cC
    cmul
    co
    #
    cD
    cmo
    co
    #
    wceq
    #
    @2
    @5
    wa
    #
    @8
    @9
    cD
    cC
    cA
    cD
    cdiv
    co
    #
    cfl
    cfv
    #
    cmul
    co
    #
    cmul
    co
    #
    cmin
    co
    #
    @11
    cD
    cC
    cB
    cD
    cdiv
    co
    #
    cfl
    cfv
    #
    cmul
    co
    #
    cmul
    co
    #
    cmin
    co
    #
    wceq
    #
    @13
    @14
    @8
    cA
    cD
    @16
    cmul
    co
    #
    cmin
    co
    #
    cC
    cmul
    co
    #
    cB
    cD
    @21
    cmul
    co
    #
    cmin
    co
    #
    cC
    cmul
    co
    #
    wceq
    #
    @25
    @14
    @8
    @27
    @30
    wceq
    #
    @32
    @2
    @4
    @8
    @33
    wb
    #
    @3
    @0
    @1
    @4
    @34
    @0
    @4
    wa
    #
    @1
    @4
    wa
    #
    @6
    @27
    @7
    @30
    cA
    cD
    modval
    cB
    cD
    modval
    eqeqan12d
    anandirs
    adantrl
    @27
    @30
    cC
    cmul
    oveq1
    syl6bi
    @14
    @19
    @28
    @24
    @31
    @0
    @5
    @19
    @28
    wceq
    @1
    @0
    @5
    wa
    #
    @19
    @9
    @26
    cC
    cmul
    co
    #
    cmin
    co
    @28
    @37
    @18
    @38
    @9
    cmin
    @37
    cD
    cC
    cmul
    co
    #
    @16
    cmul
    co
    @18
    @38
    @37
    cD
    cC
    @16
    @4
    cD
    cc
    wcel
    #
    @0
    @3
    cD
    rpcn
    #
    ad2antll
    #
    @3
    cC
    cc
    wcel
    #
    @0
    @4
    cC
    zcn
    #
    ad2antrl
    #
    @0
    @4
    @16
    cc
    wcel
    @3
    @35
    @16
    @35
    @15
    cA
    cD
    rerpdivcl
    flcld
    #
    zcnd
    #
    adantrl
    #
    mulassd
    @37
    cD
    cC
    @16
    @42
    @45
    @48
    mul32d
    eqtr3d
    oveq2d
    @37
    cA
    @26
    cC
    @0
    cA
    cc
    wcel
    @5
    cA
    recn
    adantr
    @0
    @4
    @26
    cc
    wcel
    @3
    @35
    cD
    @16
    @4
    @40
    @0
    @41
    adantl
    @47
    mulcld
    adantrl
    @45
    subdird
    eqtr4d
    adantlr
    @1
    @5
    @24
    @31
    wceq
    @0
    @1
    @5
    wa
    #
    @24
    @11
    @29
    cC
    cmul
    co
    #
    cmin
    co
    @31
    @49
    @23
    @50
    @11
    cmin
    @49
    @39
    @21
    cmul
    co
    @23
    @50
    @49
    cD
    cC
    @21
    @4
    @40
    @1
    @3
    @41
    ad2antll
    #
    @3
    @43
    @1
    @4
    @44
    ad2antrl
    #
    @1
    @4
    @21
    cc
    wcel
    @3
    @36
    @21
    @36
    @20
    cB
    cD
    rerpdivcl
    flcld
    #
    zcnd
    #
    adantrl
    #
    mulassd
    @49
    cD
    cC
    @21
    @51
    @52
    @55
    mul32d
    eqtr3d
    oveq2d
    @49
    cB
    @29
    cC
    @1
    cB
    cc
    wcel
    @5
    cB
    recn
    adantr
    @1
    @4
    @29
    cc
    wcel
    @3
    @36
    cD
    @21
    @4
    @40
    @1
    @41
    adantl
    @54
    mulcld
    adantrl
    @52
    subdird
    eqtr4d
    adantll
    eqeq12d
    sylibrd
    @25
    @19
    cD
    cmo
    co
    #
    @24
    cD
    cmo
    co
    #
    wceq
    @14
    @13
    @19
    @24
    cD
    cmo
    oveq1
    @14
    @56
    @10
    @57
    @12
    @0
    @5
    @56
    @10
    wceq
    #
    @1
    @37
    @9
    cr
    wcel
    #
    @4
    @17
    cz
    wcel
    @58
    @0
    @3
    @59
    @4
    @3
    @0
    cC
    cr
    wcel
    #
    @59
    cC
    zre
    #
    cA
    cC
    remulcl
    sylan2
    adantrr
    @0
    @3
    @4
    simprr
    @37
    cC
    @16
    @0
    @3
    @4
    simprl
    @0
    @4
    @16
    cz
    wcel
    @3
    @46
    adantrl
    zmulcld
    @9
    cD
    @17
    modcyc2
    syl3anc
    adantlr
    @1
    @5
    @57
    @12
    wceq
    #
    @0
    @49
    @11
    cr
    wcel
    #
    @4
    @22
    cz
    wcel
    @62
    @1
    @3
    @63
    @4
    @3
    @1
    @60
    @63
    @61
    cB
    cC
    remulcl
    sylan2
    adantrr
    @1
    @3
    @4
    simprr
    @49
    cC
    @21
    @1
    @3
    @4
    simprl
    @1
    @4
    @21
    cz
    wcel
    @3
    @53
    adantrl
    zmulcld
    @11
    cD
    @22
    modcyc2
    syl3anc
    adantll
    eqeq12d
    syl5ib
    syld
    3impia
end
