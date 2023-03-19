include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "cdiv.mm"
include "co.mm"
include "cmul.mm"
include "wceq.mm"
include "simprrl.mm"
include "simprll.mm"
include "simprlr.mm"
include "divcl.mm"
include "syl3anc.mm"
include "simpll.mm"
include "simplrl.mm"
include "simplrr.mm"
include "mulcomd.mm"
include "simplr.mm"
include "simprl.mm"
include "divmuldiv.mm"
include "syl22anc.mm"
include "eqtrd.mm"
include "oveq2d.mm"
include "c1.mm"
include "simprr.mm"
include "oveq1d.mm"
include "mulcld.mm"
include "simprrr.mm"
include "mulne0d.mm"
include "divid.mm"
include "syl2anc.mm"
include "mulassd.mm"
include "mulid2d.mm"
include "3eqtr3d.mm"
include "eqtr3d.mm"
include "wb.mm"
include "mulne0.mm"
include "ad2ant2lr.mm"
include "divne0.mm"
include "adantl.mm"
include "divmul.mm"
include "syl112anc.mm"
include "mpbird.mm"

theorem divdivdiv
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- ( ( ( A e. CC /\ ( B e. CC /\ B =/= 0 ) ) /\ ( ( C e. CC /\ C =/= 0 ) /\ ( D e. CC /\ D =/= 0 ) ) ) -> ( ( A / B ) / ( C / D ) ) = ( ( A x. D ) / ( B x. C ) ) )

  proof
    cA
    cc
    wcel
    #
    cB
    cc
    wcel
    #
    cB
    cc0
    wne
    #
    wa
    #
    wa
    #
    cC
    cc
    wcel
    #
    cC
    cc0
    wne
    #
    wa
    #
    cD
    cc
    wcel
    #
    cD
    cc0
    wne
    #
    wa
    #
    wa
    #
    wa
    #
    cA
    cB
    cdiv
    co
    #
    cC
    cD
    cdiv
    co
    #
    cdiv
    co
    cA
    cD
    cmul
    co
    #
    cB
    cC
    cmul
    co
    #
    cdiv
    co
    #
    wceq
    #
    @14
    @17
    cmul
    co
    #
    @13
    wceq
    #
    @12
    @14
    cD
    cC
    cdiv
    co
    #
    @13
    cmul
    co
    #
    cmul
    co
    #
    @19
    @13
    @12
    @22
    @17
    @14
    cmul
    @12
    @22
    @13
    @21
    cmul
    co
    #
    @17
    @12
    @21
    @13
    @12
    @8
    @5
    @6
    @21
    cc
    wcel
    @4
    @7
    @8
    @9
    simprrl
    #
    @4
    @5
    @6
    @10
    simprll
    #
    @4
    @5
    @6
    @10
    simprlr
    #
    cD
    cC
    divcl
    syl3anc
    #
    @12
    @0
    @1
    @2
    @13
    cc
    wcel
    #
    @0
    @3
    @11
    simpll
    #
    @0
    @1
    @2
    @11
    simplrl
    #
    @0
    @1
    @2
    @11
    simplrr
    cA
    cB
    divcl
    syl3anc
    #
    mulcomd
    @12
    @0
    @8
    @3
    @7
    @24
    @17
    wceq
    @30
    @25
    @0
    @3
    @11
    simplr
    @4
    @7
    @10
    simprl
    #
    cA
    cD
    cB
    cC
    divmuldiv
    syl22anc
    eqtrd
    oveq2d
    @12
    @14
    @21
    cmul
    co
    #
    @13
    cmul
    co
    c1
    @13
    cmul
    co
    @23
    @13
    @12
    @34
    c1
    @13
    cmul
    @12
    @34
    cC
    cD
    cmul
    co
    #
    cD
    cC
    cmul
    co
    #
    cdiv
    co
    #
    c1
    @12
    @5
    @8
    @10
    @7
    @34
    @37
    wceq
    @26
    @25
    @4
    @7
    @10
    simprr
    @33
    cC
    cD
    cD
    cC
    divmuldiv
    syl22anc
    @12
    @37
    @36
    @36
    cdiv
    co
    #
    c1
    @12
    @35
    @36
    @36
    cdiv
    @12
    cC
    cD
    @26
    @25
    mulcomd
    oveq1d
    @12
    @36
    cc
    wcel
    @36
    cc0
    wne
    @38
    c1
    wceq
    @12
    cD
    cC
    @25
    @26
    mulcld
    @12
    cD
    cC
    @25
    @26
    @4
    @7
    @8
    @9
    simprrr
    #
    @27
    mulne0d
    @36
    divid
    syl2anc
    eqtrd
    eqtrd
    oveq1d
    @12
    @14
    @21
    @13
    @12
    @5
    @8
    @9
    @14
    cc
    wcel
    #
    @26
    @25
    @39
    cC
    cD
    divcl
    syl3anc
    #
    @28
    @32
    mulassd
    @12
    @13
    @32
    mulid2d
    3eqtr3d
    eqtr3d
    @12
    @29
    @17
    cc
    wcel
    #
    @40
    @14
    cc0
    wne
    #
    @18
    @20
    wb
    @32
    @12
    @15
    cc
    wcel
    @16
    cc
    wcel
    @16
    cc0
    wne
    #
    @42
    @12
    cA
    cD
    @30
    @25
    mulcld
    @12
    cB
    cC
    @31
    @26
    mulcld
    @3
    @7
    @44
    @0
    @10
    cB
    cC
    mulne0
    ad2ant2lr
    @15
    @16
    divcl
    syl3anc
    @41
    @11
    @43
    @4
    cC
    cD
    divne0
    adantl
    @13
    @17
    @14
    divmul
    syl112anc
    mpbird
end
