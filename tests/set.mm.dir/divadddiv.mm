include "cc.mm"
include "wcel.mm"
include "wa.mm"
include "cc0.mm"
include "wne.mm"
include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "cdiv.mm"
include "wceq.mm"
include "mulcl.mm"
include "ad2ant2r.mm"
include "adantrl.mm"
include "adantrr.mm"
include "ad2ant2lr.mm"
include "mulne0.mm"
include "jca.mm"
include "adantl.mm"
include "divdir.mm"
include "syl3anc.mm"
include "simpll.mm"
include "simprr.mm"
include "simpld.mm"
include "mulcomd.mm"
include "simprll.mm"
include "oveq12d.mm"
include "simprl.mm"
include "divcan5.mm"
include "eqtrd.mm"
include "simplr.mm"
include "oveq1d.mm"
include "eqtr2d.mm"

theorem divadddiv
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- ( ( ( A e. CC /\ B e. CC ) /\ ( ( C e. CC /\ C =/= 0 ) /\ ( D e. CC /\ D =/= 0 ) ) ) -> ( ( A / C ) + ( B / D ) ) = ( ( ( A x. D ) + ( B x. C ) ) / ( C x. D ) ) )

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
    cD
    cmul
    co
    #
    cB
    cC
    cmul
    co
    #
    caddc
    co
    cC
    cD
    cmul
    co
    #
    cdiv
    co
    #
    @11
    @13
    cdiv
    co
    #
    @12
    @13
    cdiv
    co
    #
    caddc
    co
    #
    cA
    cC
    cdiv
    co
    #
    cB
    cD
    cdiv
    co
    #
    caddc
    co
    @10
    @11
    cc
    wcel
    #
    @12
    cc
    wcel
    #
    @13
    cc
    wcel
    #
    @13
    cc0
    wne
    #
    wa
    #
    @14
    @17
    wceq
    @2
    @8
    @20
    @5
    @0
    @6
    @20
    @1
    @7
    cA
    cD
    mulcl
    ad2ant2r
    adantrl
    @1
    @5
    @21
    @0
    @8
    @1
    @3
    @21
    @4
    cB
    cC
    mulcl
    adantrr
    ad2ant2lr
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
    @12
    @13
    divdir
    syl3anc
    @10
    @15
    @18
    @16
    @19
    caddc
    @10
    @15
    cD
    cA
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
    @18
    @10
    @11
    @25
    @13
    @26
    cdiv
    @10
    cA
    cD
    @0
    @1
    @9
    simpll
    #
    @10
    @6
    @7
    @2
    @5
    @8
    simprr
    #
    simpld
    #
    mulcomd
    @10
    cC
    cD
    @2
    @3
    @4
    @8
    simprll
    #
    @30
    mulcomd
    oveq12d
    @10
    @0
    @5
    @8
    @27
    @18
    wceq
    @28
    @2
    @5
    @8
    simprl
    #
    @29
    cA
    cC
    cD
    divcan5
    syl3anc
    eqtrd
    @10
    @16
    cC
    cB
    cmul
    co
    #
    @13
    cdiv
    co
    #
    @19
    @10
    @12
    @33
    @13
    cdiv
    @10
    cB
    cC
    @0
    @1
    @9
    simplr
    #
    @31
    mulcomd
    oveq1d
    @10
    @1
    @8
    @5
    @34
    @19
    wceq
    @35
    @29
    @32
    cB
    cD
    cC
    divcan5
    syl3anc
    eqtrd
    oveq12d
    eqtr2d
end
