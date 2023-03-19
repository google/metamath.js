include "con0.mm"
include "wcel.mm"
include "coe.mm"
include "co.mm"
include "comu.mm"
include "wceq.mm"
include "wa.mm"
include "c0.mm"
include "wo.mm"
include "c1o.mm"
include "oveq2.mm"
include "oe0m0.mm"
include "syl6eq.mm"
include "oveq1d.mm"
include "oe1m.mm"
include "sylan9eqr.mm"
include "adantll.mm"
include "0elon.mm"
include "oecl.mm"
include "mpan.mm"
include "oe0.mm"
include "syl.mm"
include "adantlr.mm"
include "jaodan.mm"
include "om00.mm"
include "biimpar.mm"
include "oveq2d.mm"
include "eqtr4d.mm"
include "wn.mm"
include "wne.mm"
include "on0eln0.mm"
include "bi2anan9.mm"
include "neanior.mm"
include "syl6bb.mm"
include "oe0m1.mm"
include "biimpa.mm"
include "sylan9eq.mm"
include "an4s.mm"
include "om00el.mm"
include "wb.mm"
include "omcl.mm"
include "bitr3d.mm"
include "ex.mm"
include "sylbird.mm"
include "imp.mm"
include "pm2.61dan.mm"
include "oveq1.mm"
include "eqeq12d.mm"
include "syl5ibr.mm"
include "impcom.mm"
include "wi.mm"
include "cif.mm"
include "imbi2d.mm"
include "eleq1.mm"
include "eleq2.mm"
include "anbi12d.mm"
include "1on.mm"
include "0lt1o.mm"
include "pm3.2i.mm"
include "elimhyp.mm"
include "simpli.mm"
include "simpri.mm"
include "oeoelem.mm"
include "dedth.mm"
include "an32s.mm"
include "oe0lem.mm"
include "3impb.mm"

theorem oeoe
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. On /\ B e. On /\ C e. On ) -> ( ( A ^o B ) ^o C ) = ( A ^o ( B .o C ) ) )

  proof
    cA
    con0
    wcel
    #
    cB
    con0
    wcel
    #
    cC
    con0
    wcel
    #
    cA
    cB
    coe
    co
    #
    cC
    coe
    co
    #
    cA
    cB
    cC
    comu
    co
    #
    coe
    co
    #
    wceq
    #
    @1
    @2
    wa
    #
    @7
    cA
    cA
    c0
    wceq
    #
    @8
    @7
    @8
    @7
    @9
    c0
    cB
    coe
    co
    #
    cC
    coe
    co
    #
    c0
    @5
    coe
    co
    #
    wceq
    #
    @8
    cB
    c0
    wceq
    #
    cC
    c0
    wceq
    #
    wo
    #
    @13
    @8
    @16
    wa
    #
    @11
    c1o
    @12
    @8
    @14
    @11
    c1o
    wceq
    #
    @15
    @2
    @14
    @18
    @1
    @14
    @2
    @11
    c1o
    cC
    coe
    co
    c1o
    @14
    @10
    c1o
    cC
    coe
    @14
    @10
    c0
    c0
    coe
    co
    #
    c1o
    cB
    c0
    c0
    coe
    oveq2
    oe0m0
    syl6eq
    oveq1d
    cC
    oe1m
    sylan9eqr
    adantll
    @1
    @15
    @18
    @2
    @15
    @1
    @11
    @10
    c0
    coe
    co
    #
    c1o
    cC
    c0
    @10
    coe
    oveq2
    @1
    @10
    con0
    wcel
    #
    @20
    c1o
    wceq
    c0
    con0
    wcel
    @1
    @21
    0elon
    c0
    cB
    oecl
    mpan
    @10
    oe0
    syl
    sylan9eqr
    adantlr
    jaodan
    @17
    @12
    @19
    c1o
    @17
    @5
    c0
    c0
    coe
    @8
    @5
    c0
    wceq
    @16
    cB
    cC
    om00
    biimpar
    oveq2d
    oe0m0
    syl6eq
    eqtr4d
    @8
    @16
    wn
    #
    @13
    @8
    @22
    c0
    cB
    wcel
    #
    c0
    cC
    wcel
    #
    wa
    #
    @13
    @8
    @25
    cB
    c0
    wne
    #
    cC
    c0
    wne
    #
    wa
    @22
    @1
    @23
    @26
    @2
    @24
    @27
    cB
    on0eln0
    cC
    on0eln0
    bi2anan9
    cB
    c0
    cC
    c0
    neanior
    syl6bb
    @8
    @25
    @13
    @8
    @25
    wa
    @11
    c0
    @12
    @1
    @23
    @2
    @24
    @11
    c0
    wceq
    @1
    @23
    wa
    #
    @2
    @24
    wa
    @11
    c0
    cC
    coe
    co
    #
    c0
    @28
    @10
    c0
    cC
    coe
    @1
    @23
    @10
    c0
    wceq
    cB
    oe0m1
    biimpa
    oveq1d
    @2
    @24
    @29
    c0
    wceq
    cC
    oe0m1
    biimpa
    sylan9eq
    an4s
    @8
    @25
    @12
    c0
    wceq
    #
    @8
    c0
    @5
    wcel
    #
    @25
    @30
    cB
    cC
    om00el
    @8
    @5
    con0
    wcel
    @31
    @30
    wb
    cB
    cC
    omcl
    @5
    oe0m1
    syl
    bitr3d
    biimpa
    eqtr4d
    ex
    sylbird
    imp
    pm2.61dan
    @9
    @4
    @11
    @6
    @12
    @9
    @3
    @10
    cC
    coe
    cA
    c0
    cB
    coe
    oveq1
    oveq1d
    cA
    c0
    @5
    coe
    oveq1
    eqeq12d
    syl5ibr
    impcom
    @0
    c0
    cA
    wcel
    #
    @8
    @7
    @0
    @32
    wa
    #
    @8
    @7
    @33
    @8
    @7
    wi
    @8
    @33
    cA
    c1o
    cif
    #
    cB
    coe
    co
    #
    cC
    coe
    co
    #
    @34
    @5
    coe
    co
    #
    wceq
    #
    wi
    cA
    c1o
    cA
    @34
    wceq
    #
    @7
    @38
    @8
    @39
    @4
    @36
    @6
    @37
    @39
    @3
    @35
    cC
    coe
    cA
    @34
    cB
    coe
    oveq1
    oveq1d
    cA
    @34
    @5
    coe
    oveq1
    eqeq12d
    imbi2d
    @34
    cB
    cC
    @34
    con0
    wcel
    #
    c0
    @34
    wcel
    #
    @33
    @40
    @41
    wa
    c1o
    con0
    wcel
    #
    c0
    c1o
    wcel
    #
    wa
    cA
    c1o
    @39
    @0
    @40
    @32
    @41
    cA
    @34
    con0
    eleq1
    cA
    @34
    c0
    eleq2
    anbi12d
    c1o
    @34
    wceq
    @42
    @40
    @43
    @41
    c1o
    @34
    con0
    eleq1
    c1o
    @34
    c0
    eleq2
    anbi12d
    @42
    @43
    1on
    0lt1o
    pm3.2i
    elimhyp
    #
    simpli
    @40
    @41
    @44
    simpri
    oeoelem
    dedth
    imp
    an32s
    oe0lem
    3impb
end
