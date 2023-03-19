include "cc.mm"
include "wcel.mm"
include "wa.mm"
include "cc0.mm"
include "wne.mm"
include "cdiv.mm"
include "co.mm"
include "cmul.mm"
include "wceq.mm"
include "wb.mm"
include "divcl.mm"
include "3expb.mm"
include "ad2ant2r.mm"
include "ad2ant2l.mm"
include "mulcl.mm"
include "mulne0.mm"
include "jca.mm"
include "adantl.mm"
include "mulcan2.mm"
include "syl3anc.mm"
include "simprll.mm"
include "simprrl.mm"
include "mulassd.mm"
include "divcan1.mm"
include "oveq1d.mm"
include "eqtr3d.mm"
include "mulcomd.mm"
include "oveq2d.mm"
include "3eqtr2d.mm"
include "eqeq12d.mm"
include "bitr3d.mm"

theorem divmuleq
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- ( ( ( A e. CC /\ B e. CC ) /\ ( ( C e. CC /\ C =/= 0 ) /\ ( D e. CC /\ D =/= 0 ) ) ) -> ( ( A / C ) = ( B / D ) <-> ( A x. D ) = ( B x. C ) ) )

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
    cC
    cdiv
    co
    #
    cC
    cD
    cmul
    co
    #
    cmul
    co
    #
    cB
    cD
    cdiv
    co
    #
    @12
    cmul
    co
    #
    wceq
    #
    @11
    @14
    wceq
    #
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
    wceq
    @10
    @11
    cc
    wcel
    #
    @14
    cc
    wcel
    #
    @12
    cc
    wcel
    #
    @12
    cc0
    wne
    #
    wa
    #
    @16
    @17
    wb
    @0
    @5
    @20
    @1
    @8
    @0
    @3
    @4
    @20
    cA
    cC
    divcl
    3expb
    ad2ant2r
    #
    @1
    @8
    @21
    @0
    @5
    @1
    @6
    @7
    @21
    cB
    cD
    divcl
    3expb
    ad2ant2l
    #
    @9
    @24
    @2
    @9
    @22
    @23
    @3
    @6
    @22
    @4
    @7
    cC
    cD
    mulcl
    ad2ant2r
    cC
    cD
    mulne0
    jca
    adantl
    @11
    @14
    @12
    mulcan2
    syl3anc
    @10
    @13
    @18
    @15
    @19
    @10
    @11
    cC
    cmul
    co
    #
    cD
    cmul
    co
    @13
    @18
    @10
    @11
    cC
    cD
    @25
    @2
    @3
    @4
    @8
    simprll
    #
    @2
    @5
    @6
    @7
    simprrl
    #
    mulassd
    @10
    @27
    cA
    cD
    cmul
    @0
    @5
    @27
    cA
    wceq
    #
    @1
    @8
    @0
    @3
    @4
    @30
    cA
    cC
    divcan1
    3expb
    ad2ant2r
    oveq1d
    eqtr3d
    @10
    @15
    @14
    cD
    cC
    cmul
    co
    #
    cmul
    co
    @14
    cD
    cmul
    co
    #
    cC
    cmul
    co
    @19
    @10
    @12
    @31
    @14
    cmul
    @10
    cC
    cD
    @28
    @29
    mulcomd
    oveq2d
    @10
    @14
    cD
    cC
    @26
    @29
    @28
    mulassd
    @10
    @32
    cB
    cC
    cmul
    @1
    @8
    @32
    cB
    wceq
    #
    @0
    @5
    @1
    @6
    @7
    @33
    cB
    cD
    divcan1
    3expb
    ad2ant2l
    oveq1d
    3eqtr2d
    eqeq12d
    bitr3d
end
