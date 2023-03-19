include "cz.mm"
include "wcel.mm"
include "wa.mm"
include "cn0.mm"
include "crp.mm"
include "cmo.mm"
include "co.mm"
include "wceq.mm"
include "w3a.mm"
include "cexp.mm"
include "simp2l.mm"
include "id.mm"
include "3adant2l.mm"
include "cv.mm"
include "wi.mm"
include "cc0.mm"
include "c1.mm"
include "caddc.mm"
include "oveq2.mm"
include "oveq1d.mm"
include "eqeq12d.mm"
include "imbi2d.mm"
include "cc.mm"
include "zcn.mm"
include "exp0.mm"
include "syl.mm"
include "eqcomd.mm"
include "sylan9eq.mm"
include "3ad2ant1.mm"
include "cmul.mm"
include "simp21l.mm"
include "simp1.mm"
include "zexpcl.mm"
include "syl2anc.mm"
include "simp21r.mm"
include "simp22.mm"
include "simp3.mm"
include "simp23.mm"
include "modmul12d.mm"
include "zcnd.mm"
include "expp1.mm"
include "3eqtr4d.mm"
include "3exp.mm"
include "a2d.mm"
include "nn0ind.mm"
include "sylc.mm"

theorem modexp
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( ( A e. ZZ /\ B e. ZZ ) /\ ( C e. NN0 /\ D e. RR+ ) /\ ( A mod D ) = ( B mod D ) ) -> ( ( A ^ C ) mod D ) = ( ( B ^ C ) mod D ) )

  proof
    cA
    cz
    wcel
    #
    cB
    cz
    wcel
    #
    wa
    #
    cC
    cn0
    wcel
    #
    cD
    crp
    wcel
    #
    wa
    cA
    cD
    cmo
    co
    cB
    cD
    cmo
    co
    wceq
    #
    w3a
    @3
    @2
    @4
    @5
    w3a
    #
    cA
    cC
    cexp
    co
    #
    cD
    cmo
    co
    #
    cB
    cC
    cexp
    co
    #
    cD
    cmo
    co
    #
    wceq
    #
    @2
    @3
    @4
    @5
    simp2l
    @2
    @4
    @5
    @6
    @3
    @6
    id
    3adant2l
    @6
    cA
    vx
    cv
    #
    cexp
    co
    #
    cD
    cmo
    co
    #
    cB
    @12
    cexp
    co
    #
    cD
    cmo
    co
    #
    wceq
    #
    wi
    @6
    cA
    cc0
    cexp
    co
    #
    cD
    cmo
    co
    #
    cB
    cc0
    cexp
    co
    #
    cD
    cmo
    co
    #
    wceq
    #
    wi
    @6
    cA
    vk
    cv
    #
    cexp
    co
    #
    cD
    cmo
    co
    #
    cB
    @23
    cexp
    co
    #
    cD
    cmo
    co
    #
    wceq
    #
    wi
    @6
    cA
    @23
    c1
    caddc
    co
    #
    cexp
    co
    #
    cD
    cmo
    co
    #
    cB
    @29
    cexp
    co
    #
    cD
    cmo
    co
    #
    wceq
    #
    wi
    @6
    @11
    wi
    vx
    vk
    cC
    @12
    cc0
    wceq
    #
    @17
    @22
    @6
    @35
    @14
    @19
    @16
    @21
    @35
    @13
    @18
    cD
    cmo
    @12
    cc0
    cA
    cexp
    oveq2
    oveq1d
    @35
    @15
    @20
    cD
    cmo
    @12
    cc0
    cB
    cexp
    oveq2
    oveq1d
    eqeq12d
    imbi2d
    @12
    @23
    wceq
    #
    @17
    @28
    @6
    @36
    @14
    @25
    @16
    @27
    @36
    @13
    @24
    cD
    cmo
    @12
    @23
    cA
    cexp
    oveq2
    oveq1d
    @36
    @15
    @26
    cD
    cmo
    @12
    @23
    cB
    cexp
    oveq2
    oveq1d
    eqeq12d
    imbi2d
    @12
    @29
    wceq
    #
    @17
    @34
    @6
    @37
    @14
    @31
    @16
    @33
    @37
    @13
    @30
    cD
    cmo
    @12
    @29
    cA
    cexp
    oveq2
    oveq1d
    @37
    @15
    @32
    cD
    cmo
    @12
    @29
    cB
    cexp
    oveq2
    oveq1d
    eqeq12d
    imbi2d
    @12
    cC
    wceq
    #
    @17
    @11
    @6
    @38
    @14
    @8
    @16
    @10
    @38
    @13
    @7
    cD
    cmo
    @12
    cC
    cA
    cexp
    oveq2
    oveq1d
    @38
    @15
    @9
    cD
    cmo
    @12
    cC
    cB
    cexp
    oveq2
    oveq1d
    eqeq12d
    imbi2d
    @2
    @4
    @22
    @5
    @2
    @18
    @20
    cD
    cmo
    @0
    @1
    @18
    c1
    @20
    @0
    cA
    cc
    wcel
    #
    @18
    c1
    wceq
    cA
    zcn
    cA
    exp0
    syl
    @1
    @20
    c1
    @1
    cB
    cc
    wcel
    #
    @20
    c1
    wceq
    cB
    zcn
    cB
    exp0
    syl
    eqcomd
    sylan9eq
    oveq1d
    3ad2ant1
    @23
    cn0
    wcel
    #
    @6
    @28
    @34
    @41
    @6
    @28
    @34
    @41
    @6
    @28
    w3a
    #
    @24
    cA
    cmul
    co
    #
    cD
    cmo
    co
    @26
    cB
    cmul
    co
    #
    cD
    cmo
    co
    @31
    @33
    @42
    @24
    @26
    cA
    cB
    cD
    @42
    @0
    @41
    @24
    cz
    wcel
    @0
    @1
    @4
    @5
    @41
    @28
    simp21l
    #
    @41
    @6
    @28
    simp1
    #
    cA
    @23
    zexpcl
    syl2anc
    @42
    @1
    @41
    @26
    cz
    wcel
    @0
    @1
    @4
    @5
    @41
    @28
    simp21r
    #
    @46
    cB
    @23
    zexpcl
    syl2anc
    @45
    @47
    @41
    @2
    @4
    @5
    @28
    simp22
    @41
    @6
    @28
    simp3
    @41
    @2
    @4
    @5
    @28
    simp23
    modmul12d
    @42
    @30
    @43
    cD
    cmo
    @42
    @39
    @41
    @30
    @43
    wceq
    @42
    cA
    @45
    zcnd
    @46
    cA
    @23
    expp1
    syl2anc
    oveq1d
    @42
    @32
    @44
    cD
    cmo
    @42
    @40
    @41
    @32
    @44
    wceq
    @42
    cB
    @47
    zcnd
    @46
    cB
    @23
    expp1
    syl2anc
    oveq1d
    3eqtr4d
    3exp
    a2d
    nn0ind
    sylc
end
