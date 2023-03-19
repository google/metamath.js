include "cv.mm"
include "cz.mm"
include "wcel.mm"
include "wss.mm"
include "cfn.mm"
include "w3a.mm"
include "cdvds.mm"
include "wbr.mm"
include "wral.mm"
include "clcmf.mm"
include "cfv.mm"
include "wi.mm"
include "csn.mm"
include "cun.mm"
include "clcm.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "nfv.mm"
include "nfra1.mm"
include "nfan.mm"
include "breq2.mm"
include "ralbidv.mm"
include "imbi12d.mm"
include "cbvralv.mm"
include "rspcv.mm"
include "adantl.mm"
include "sneq.mm"
include "uneq2d.mm"
include "fveq2d.mm"
include "oveq2.mm"
include "eqeq12d.mm"
include "3ad2ant1.mm"
include "adantr.mm"
include "simpr.mm"
include "lcmfcl.mm"
include "nn0zd.mm"
include "3adant1.mm"
include "simpl1.mm"
include "3jca.mm"
include "ssun1.mm"
include "ssralv.mm"
include "mp1i.mm"
include "imim1d.mm"
include "imp31.mm"
include "wo.mm"
include "snidg.mm"
include "olcd.mm"
include "elun.mm"
include "sylibr.mm"
include "breq1.mm"
include "syl.mm"
include "imp.mm"
include "jca.mm"
include "lcmdvds.mm"
include "sylc.mm"
include "syl5ibrcom.mm"
include "ex.mm"
include "com23.mm"
include "syl5d.mm"
include "syld.mm"
include "syl5bi.mm"
include "impd.mm"
include "impancom.mm"
include "ralrimi.mm"

theorem lcmfunsnlem1
  let vy: setvar y
  let vz: setvar z
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let vx: setvar x
  let vl: setvar l

  disjoint m y
  disjoint m z
  disjoint y z
  disjoint k n
  disjoint k y
  disjoint k z
  disjoint n y
  disjoint n z
  disjoint k m
  disjoint m x
  disjoint x y
  disjoint x z
  disjoint k x
  disjoint n x
  disjoint k l
  disjoint l m
  disjoint l y
  assert |- ( ( ( z e. ZZ /\ y C_ ZZ /\ y e. Fin ) /\ ( A. k e. ZZ ( A. m e. y m || k -> ( _lcm ` y ) || k ) /\ A. n e. ZZ ( _lcm ` ( y u. { n } ) ) = ( ( _lcm ` y ) lcm n ) ) ) -> A. k e. ZZ ( A. m e. ( y u. { z } ) m || k -> ( _lcm ` ( y u. { z } ) ) || k ) )

  proof
    vz
    cv
    #
    cz
    wcel
    #
    vy
    cv
    #
    cz
    wss
    #
    @2
    cfn
    wcel
    #
    w3a
    #
    vm
    cv
    #
    vk
    cv
    #
    cdvds
    wbr
    #
    vm
    @2
    wral
    #
    @2
    clcmf
    cfv
    #
    @7
    cdvds
    wbr
    #
    wi
    #
    vk
    cz
    wral
    #
    @2
    vn
    cv
    #
    csn
    #
    cun
    #
    clcmf
    cfv
    #
    @10
    @14
    clcm
    co
    #
    wceq
    #
    vn
    cz
    wral
    #
    wa
    #
    wa
    @8
    vm
    @2
    @0
    csn
    #
    cun
    #
    wral
    #
    @23
    clcmf
    cfv
    #
    @7
    cdvds
    wbr
    #
    wi
    #
    vk
    cz
    @5
    @21
    vk
    @5
    vk
    nfv
    @13
    @20
    vk
    @12
    vk
    cz
    nfra1
    @20
    vk
    nfv
    nfan
    nfan
    @5
    @7
    cz
    wcel
    #
    @21
    @27
    @5
    @28
    wa
    #
    @13
    @20
    @27
    @13
    @6
    vl
    cv
    #
    cdvds
    wbr
    #
    vm
    @2
    wral
    #
    @10
    @30
    cdvds
    wbr
    #
    wi
    #
    vl
    cz
    wral
    #
    @29
    @20
    @27
    wi
    #
    @12
    @34
    vk
    vl
    cz
    @7
    @30
    wceq
    #
    @9
    @32
    @11
    @33
    @37
    @8
    @31
    vm
    @2
    @7
    @30
    @6
    cdvds
    breq2
    ralbidv
    @7
    @30
    @10
    cdvds
    breq2
    imbi12d
    cbvralv
    @29
    @35
    @12
    @36
    @28
    @35
    @12
    wi
    @5
    @34
    @12
    vl
    @7
    cz
    @30
    @7
    wceq
    #
    @32
    @9
    @33
    @11
    @38
    @31
    @8
    vm
    @2
    @30
    @7
    @6
    cdvds
    breq2
    ralbidv
    @30
    @7
    @10
    cdvds
    breq2
    imbi12d
    rspcv
    adantl
    @29
    @20
    @25
    @10
    @0
    clcm
    co
    #
    wceq
    #
    @12
    @27
    @5
    @20
    @40
    wi
    #
    @28
    @1
    @3
    @41
    @4
    @19
    @40
    vn
    @0
    cz
    @14
    @0
    wceq
    #
    @17
    @25
    @18
    @39
    @42
    @16
    @23
    clcmf
    @42
    @15
    @22
    @2
    @14
    @0
    sneq
    uneq2d
    fveq2d
    @14
    @0
    @10
    clcm
    oveq2
    eqeq12d
    rspcv
    3ad2ant1
    adantr
    @29
    @12
    @40
    @27
    wi
    @29
    @12
    wa
    #
    @24
    @40
    @26
    @43
    @24
    @40
    @26
    wi
    @43
    @24
    wa
    #
    @26
    @40
    @39
    @7
    cdvds
    wbr
    #
    @44
    @28
    @10
    cz
    wcel
    #
    @1
    w3a
    #
    @11
    @0
    @7
    cdvds
    wbr
    #
    wa
    @45
    @43
    @47
    @24
    @29
    @47
    @12
    @29
    @28
    @46
    @1
    @5
    @28
    simpr
    @5
    @46
    @28
    @3
    @4
    @46
    @1
    @3
    @4
    wa
    @10
    @2
    lcmfcl
    nn0zd
    3adant1
    adantr
    @1
    @3
    @4
    @28
    simpl1
    3jca
    adantr
    adantr
    @44
    @11
    @48
    @29
    @12
    @24
    @11
    @29
    @24
    @9
    @11
    @2
    @23
    wss
    @24
    @9
    wi
    @29
    @2
    @22
    ssun1
    @8
    vm
    @2
    @23
    ssralv
    mp1i
    imim1d
    imp31
    @43
    @24
    @48
    @29
    @24
    @48
    wi
    #
    @12
    @5
    @49
    @28
    @1
    @3
    @49
    @4
    @1
    @0
    @23
    wcel
    #
    @49
    @1
    @0
    @2
    wcel
    #
    @0
    @22
    wcel
    #
    wo
    @50
    @1
    @52
    @51
    @0
    cz
    snidg
    olcd
    @0
    @2
    @22
    elun
    sylibr
    @8
    @48
    vm
    @0
    @23
    @6
    @0
    @7
    cdvds
    breq1
    rspcv
    syl
    3ad2ant1
    adantr
    adantr
    imp
    jca
    @7
    @10
    @0
    lcmdvds
    sylc
    @25
    @39
    @7
    cdvds
    breq1
    syl5ibrcom
    ex
    com23
    ex
    syl5d
    syld
    syl5bi
    impd
    impancom
    ralrimi
end
