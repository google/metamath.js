include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "crp.mm"
include "cmo.mm"
include "co.mm"
include "wceq.mm"
include "caddc.mm"
include "cdiv.mm"
include "cfl.mm"
include "cfv.mm"
include "cmul.mm"
include "cmin.mm"
include "wb.mm"
include "modval.mm"
include "eqeqan12d.mm"
include "anandirs.mm"
include "adantrl.mm"
include "oveq1.mm"
include "syl6bi.mm"
include "cc.mm"
include "recn.mm"
include "adantr.mm"
include "ad2antrl.mm"
include "rpcn.mm"
include "adantl.mm"
include "rerpdivcl.mm"
include "reflcl.mm"
include "recnd.mm"
include "syl.mm"
include "mulcld.mm"
include "addsubd.mm"
include "adantlr.mm"
include "adantll.mm"
include "eqeq12d.mm"
include "sylibrd.mm"
include "cz.mm"
include "readdcl.mm"
include "adantrr.mm"
include "simprr.mm"
include "flcld.mm"
include "modcyc2.mm"
include "syl3anc.mm"
include "syl5ib.mm"
include "syld.mm"
include "3impia.mm"

theorem modadd1
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- ( ( ( A e. RR /\ B e. RR ) /\ ( C e. RR /\ D e. RR+ ) /\ ( A mod D ) = ( B mod D ) ) -> ( ( A + C ) mod D ) = ( ( B + C ) mod D ) )

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
    cr
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
    caddc
    co
    #
    cD
    cmo
    co
    #
    cB
    cC
    caddc
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
    cmin
    co
    #
    @11
    cD
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
    cmin
    co
    #
    wceq
    #
    @13
    @14
    @8
    cA
    @17
    cmin
    co
    #
    cC
    caddc
    co
    #
    cB
    @21
    cmin
    co
    #
    cC
    caddc
    co
    #
    wceq
    #
    @23
    @14
    @8
    @24
    @26
    wceq
    #
    @28
    @2
    @4
    @8
    @29
    wb
    #
    @3
    @0
    @1
    @4
    @30
    @0
    @4
    wa
    #
    @1
    @4
    wa
    #
    @6
    @24
    @7
    @26
    cA
    cD
    modval
    cB
    cD
    modval
    eqeqan12d
    anandirs
    adantrl
    @24
    @26
    cC
    caddc
    oveq1
    syl6bi
    @14
    @18
    @25
    @22
    @27
    @0
    @5
    @18
    @25
    wceq
    @1
    @0
    @5
    wa
    #
    cA
    cC
    @17
    @0
    cA
    cc
    wcel
    @5
    cA
    recn
    adantr
    @3
    cC
    cc
    wcel
    #
    @0
    @4
    cC
    recn
    #
    ad2antrl
    @0
    @4
    @17
    cc
    wcel
    @3
    @31
    cD
    @16
    @4
    cD
    cc
    wcel
    #
    @0
    cD
    rpcn
    #
    adantl
    @31
    @15
    cr
    wcel
    #
    @16
    cc
    wcel
    cA
    cD
    rerpdivcl
    #
    @38
    @16
    @15
    reflcl
    recnd
    syl
    mulcld
    adantrl
    addsubd
    adantlr
    @1
    @5
    @22
    @27
    wceq
    @0
    @1
    @5
    wa
    #
    cB
    cC
    @21
    @1
    cB
    cc
    wcel
    @5
    cB
    recn
    adantr
    @3
    @34
    @1
    @4
    @35
    ad2antrl
    @1
    @4
    @21
    cc
    wcel
    @3
    @32
    cD
    @20
    @4
    @36
    @1
    @37
    adantl
    @32
    @19
    cr
    wcel
    #
    @20
    cc
    wcel
    cB
    cD
    rerpdivcl
    #
    @41
    @20
    @19
    reflcl
    recnd
    syl
    mulcld
    adantrl
    addsubd
    adantll
    eqeq12d
    sylibrd
    @23
    @18
    cD
    cmo
    co
    #
    @22
    cD
    cmo
    co
    #
    wceq
    @14
    @13
    @18
    @22
    cD
    cmo
    oveq1
    @14
    @43
    @10
    @44
    @12
    @0
    @5
    @43
    @10
    wceq
    #
    @1
    @33
    @9
    cr
    wcel
    #
    @4
    @16
    cz
    wcel
    #
    @45
    @0
    @3
    @46
    @4
    cA
    cC
    readdcl
    adantrr
    @0
    @3
    @4
    simprr
    @0
    @4
    @47
    @3
    @31
    @15
    @39
    flcld
    adantrl
    @9
    cD
    @16
    modcyc2
    syl3anc
    adantlr
    @1
    @5
    @44
    @12
    wceq
    #
    @0
    @40
    @11
    cr
    wcel
    #
    @4
    @20
    cz
    wcel
    #
    @48
    @1
    @3
    @49
    @4
    cB
    cC
    readdcl
    adantrr
    @1
    @3
    @4
    simprr
    @1
    @4
    @50
    @3
    @32
    @19
    @42
    flcld
    adantrl
    @11
    cD
    @20
    modcyc2
    syl3anc
    adantll
    eqeq12d
    syl5ib
    syld
    3impia
end
