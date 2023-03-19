include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "cdiv.mm"
include "co.mm"
include "cmul.mm"
include "wceq.mm"
include "w3a.mm"
include "3anass.mm"
include "divcl.mm"
include "mulcl.mm"
include "syl2an.mm"
include "ad2ant2r.mm"
include "3adantr1.mm"
include "3adantl1.mm"
include "mulne0.mm"
include "divcan3.mm"
include "syl3anc.mm"
include "simp2.mm"
include "jca.mm"
include "mul4.mm"
include "divcan2.mm"
include "oveqan12d.mm"
include "eqtr3d.mm"
include "oveq1d.mm"
include "syl2anbr.mm"
include "an4s.mm"

theorem divmuldiv
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- ( ( ( A e. CC /\ B e. CC ) /\ ( ( C e. CC /\ C =/= 0 ) /\ ( D e. CC /\ D =/= 0 ) ) ) -> ( ( A / C ) x. ( B / D ) ) = ( ( A x. B ) / ( C x. D ) ) )

  proof
    cA
    cc
    wcel
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
    cB
    cc
    wcel
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
    cmul
    co
    #
    cA
    cB
    cmul
    co
    #
    cC
    cD
    cmul
    co
    #
    cdiv
    co
    #
    wceq
    #
    @0
    @3
    wa
    @0
    @1
    @2
    w3a
    #
    @4
    @5
    @6
    w3a
    #
    @14
    @4
    @7
    wa
    @0
    @1
    @2
    3anass
    @4
    @5
    @6
    3anass
    @15
    @16
    wa
    #
    @12
    @10
    cmul
    co
    #
    @12
    cdiv
    co
    #
    @10
    @13
    @17
    @10
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
    @19
    @10
    wceq
    @15
    @8
    cc
    wcel
    #
    @9
    cc
    wcel
    #
    @20
    @16
    cA
    cC
    divcl
    #
    cB
    cD
    divcl
    #
    @8
    @9
    mulcl
    syl2an
    @1
    @2
    @16
    @21
    @0
    @3
    @5
    @6
    @21
    @4
    @1
    @5
    @21
    @2
    @6
    cC
    cD
    mulcl
    ad2ant2r
    3adantr1
    3adantl1
    @1
    @2
    @16
    @22
    @0
    @3
    @5
    @6
    @22
    @4
    cC
    cD
    mulne0
    3adantr1
    3adantl1
    @10
    @12
    divcan3
    syl3anc
    @17
    @18
    @11
    @12
    cdiv
    @17
    cC
    @8
    cmul
    co
    #
    cD
    @9
    cmul
    co
    #
    cmul
    co
    #
    @18
    @11
    @15
    @1
    @23
    wa
    @5
    @24
    wa
    @29
    @18
    wceq
    @16
    @15
    @1
    @23
    @0
    @1
    @2
    simp2
    @25
    jca
    @16
    @5
    @24
    @4
    @5
    @6
    simp2
    @26
    jca
    cC
    @8
    cD
    @9
    mul4
    syl2an
    @15
    @16
    @27
    cA
    @28
    cB
    cmul
    cA
    cC
    divcan2
    cB
    cD
    divcan2
    oveqan12d
    eqtr3d
    oveq1d
    eqtr3d
    syl2anbr
    an4s
end
