include "cn.mm"
include "wcel.mm"
include "cgcd.mm"
include "co.mm"
include "c1.mm"
include "wceq.mm"
include "cexp.mm"
include "wi.mm"
include "wa.mm"
include "cv.mm"
include "caddc.mm"
include "oveq2.mm"
include "oveq1d.mm"
include "eqeq1d.mm"
include "imbi2d.mm"
include "weq.mm"
include "nncn.mm"
include "exp1d.mm"
include "adantr.mm"
include "biimpar.mm"
include "w3a.mm"
include "df-3an.mm"
include "cmul.mm"
include "simpl1.mm"
include "nncnd.mm"
include "simpl3.mm"
include "nnnn0d.mm"
include "expp1d.mm"
include "cz.mm"
include "simp1.mm"
include "cn0.mm"
include "nnnn0.mm"
include "3ad2ant3.mm"
include "nnexpcld.mm"
include "nnzd.mm"
include "zcnd.mm"
include "mulcomd.mm"
include "eqtrd.mm"
include "oveq2d.mm"
include "simpl2.mm"
include "nnz.mm"
include "3ad2ant1.mm"
include "3ad2ant2.mm"
include "gcdcom.mm"
include "syl2anc.mm"
include "biimpa.mm"
include "rpmulgcd.mm"
include "syl31anc.mm"
include "peano2nn.mm"
include "3eqtr4d.mm"
include "biimprd.mm"
include "sylanbr.mm"
include "an32s.mm"
include "expcom.mm"
include "a2d.mm"
include "nnind.mm"
include "expd.mm"
include "com12.mm"
include "3impia.mm"

theorem rplpwr
  let cA: class A
  let cB: class B
  let cN: class N
  let vn: setvar n
  let vk: setvar k


  assert |- ( ( A e. NN /\ B e. NN /\ N e. NN ) -> ( ( A gcd B ) = 1 -> ( ( A ^ N ) gcd B ) = 1 ) )

  proof
    cA
    cn
    wcel
    #
    cB
    cn
    wcel
    #
    cN
    cn
    wcel
    #
    cA
    cB
    cgcd
    co
    #
    c1
    wceq
    #
    cA
    cN
    cexp
    co
    #
    cB
    cgcd
    co
    #
    c1
    wceq
    #
    wi
    #
    @2
    @0
    @1
    wa
    #
    @8
    @2
    @9
    @4
    @7
    @9
    @4
    wa
    #
    cA
    vk
    cv
    #
    cexp
    co
    #
    cB
    cgcd
    co
    #
    c1
    wceq
    #
    wi
    @10
    cA
    c1
    cexp
    co
    #
    cB
    cgcd
    co
    #
    c1
    wceq
    #
    wi
    @10
    cA
    vn
    cv
    #
    cexp
    co
    #
    cB
    cgcd
    co
    #
    c1
    wceq
    #
    wi
    @10
    cA
    @18
    c1
    caddc
    co
    #
    cexp
    co
    #
    cB
    cgcd
    co
    #
    c1
    wceq
    #
    wi
    @10
    @7
    wi
    vk
    vn
    cN
    @11
    c1
    wceq
    #
    @14
    @17
    @10
    @26
    @13
    @16
    c1
    @26
    @12
    @15
    cB
    cgcd
    @11
    c1
    cA
    cexp
    oveq2
    oveq1d
    eqeq1d
    imbi2d
    vk
    vn
    weq
    #
    @14
    @21
    @10
    @27
    @13
    @20
    c1
    @27
    @12
    @19
    cB
    cgcd
    @11
    @18
    cA
    cexp
    oveq2
    oveq1d
    eqeq1d
    imbi2d
    @11
    @22
    wceq
    #
    @14
    @25
    @10
    @28
    @13
    @24
    c1
    @28
    @12
    @23
    cB
    cgcd
    @11
    @22
    cA
    cexp
    oveq2
    oveq1d
    eqeq1d
    imbi2d
    @11
    cN
    wceq
    #
    @14
    @7
    @10
    @29
    @13
    @6
    c1
    @29
    @12
    @5
    cB
    cgcd
    @11
    cN
    cA
    cexp
    oveq2
    oveq1d
    eqeq1d
    imbi2d
    @9
    @17
    @4
    @9
    @16
    @3
    c1
    @0
    @16
    @3
    wceq
    @1
    @0
    @15
    cA
    cB
    cgcd
    @0
    cA
    cA
    nncn
    exp1d
    oveq1d
    adantr
    eqeq1d
    biimpar
    @18
    cn
    wcel
    #
    @10
    @21
    @25
    @10
    @30
    @21
    @25
    wi
    #
    @9
    @30
    @4
    @31
    @9
    @30
    wa
    @0
    @1
    @30
    w3a
    #
    @4
    @31
    @0
    @1
    @30
    df-3an
    @32
    @4
    wa
    #
    @25
    @21
    @33
    @24
    @20
    c1
    @33
    cB
    @23
    cgcd
    co
    #
    cB
    @19
    cgcd
    co
    #
    @24
    @20
    @33
    @34
    cB
    cA
    @19
    cmul
    co
    #
    cgcd
    co
    #
    @35
    @33
    @23
    @36
    cB
    cgcd
    @33
    @23
    @19
    cA
    cmul
    co
    @36
    @33
    cA
    @18
    @33
    cA
    @0
    @1
    @30
    @4
    simpl1
    #
    nncnd
    #
    @33
    @18
    @0
    @1
    @30
    @4
    simpl3
    nnnn0d
    expp1d
    @33
    @19
    cA
    @33
    @19
    @32
    @19
    cz
    wcel
    #
    @4
    @32
    @19
    @32
    cA
    @18
    @0
    @1
    @30
    simp1
    @30
    @0
    @18
    cn0
    wcel
    @1
    @18
    nnnn0
    3ad2ant3
    nnexpcld
    #
    nnzd
    adantr
    #
    zcnd
    @39
    mulcomd
    eqtrd
    oveq2d
    @33
    @1
    @0
    @19
    cn
    wcel
    #
    cB
    cA
    cgcd
    co
    #
    c1
    wceq
    #
    @37
    @35
    wceq
    @0
    @1
    @30
    @4
    simpl2
    @38
    @32
    @43
    @4
    @41
    adantr
    @32
    @4
    @45
    @32
    @3
    @44
    c1
    @32
    cA
    cz
    wcel
    #
    cB
    cz
    wcel
    #
    @3
    @44
    wceq
    @0
    @1
    @46
    @30
    cA
    nnz
    3ad2ant1
    @1
    @0
    @47
    @30
    cB
    nnz
    3ad2ant2
    #
    cA
    cB
    gcdcom
    syl2anc
    eqeq1d
    biimpa
    cB
    cA
    @19
    rpmulgcd
    syl31anc
    eqtrd
    @33
    @23
    cz
    wcel
    @47
    @24
    @34
    wceq
    @33
    @23
    @33
    cA
    @22
    @38
    @33
    @22
    @32
    @22
    cn
    wcel
    #
    @4
    @30
    @0
    @49
    @1
    @18
    peano2nn
    3ad2ant3
    adantr
    nnnn0d
    nnexpcld
    nnzd
    @32
    @47
    @4
    @48
    adantr
    #
    @23
    cB
    gcdcom
    syl2anc
    @33
    @40
    @47
    @20
    @35
    wceq
    @42
    @50
    @19
    cB
    gcdcom
    syl2anc
    3eqtr4d
    eqeq1d
    biimprd
    sylanbr
    an32s
    expcom
    a2d
    nnind
    expd
    com12
    3impia
end
