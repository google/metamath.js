include "con0.mm"
include "wcel.mm"
include "coa.mm"
include "co.mm"
include "coe.mm"
include "comu.mm"
include "wceq.mm"
include "wa.mm"
include "c0.mm"
include "oa00.mm"
include "biimpar.mm"
include "oveq2d.mm"
include "c1o.mm"
include "oveq2.mm"
include "oe0m0.mm"
include "syl6eq.mm"
include "oveqan12d.mm"
include "0elon.mm"
include "oecl.mm"
include "mp2an.mm"
include "om1.mm"
include "ax-mp.mm"
include "adantl.mm"
include "eqtr4d.mm"
include "wn.mm"
include "wne.mm"
include "wb.mm"
include "oacl.mm"
include "on0eln0.mm"
include "syl.mm"
include "oe0m1.mm"
include "necon3abid.mm"
include "3bitr3d.mm"
include "wo.mm"
include "adantr.mm"
include "orbi12d.mm"
include "neorian.mm"
include "syl6bb.mm"
include "biimpa.mm"
include "oveq1d.mm"
include "mpan.mm"
include "om0r.mm"
include "sylan9eq.mm"
include "an32s.mm"
include "om0.mm"
include "sylan9eqr.mm"
include "anassrs.mm"
include "jaodan.mm"
include "ex.mm"
include "sylbird.mm"
include "imp.mm"
include "pm2.61dan.mm"
include "oveq1.mm"
include "oveq12d.mm"
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
include "elimel.mm"
include "oeoalem.mm"
include "dedth2h.mm"
include "impr.mm"
include "oe0lem.mm"
include "3impb.mm"

theorem oeoa
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. On /\ B e. On /\ C e. On ) -> ( A ^o ( B +o C ) ) = ( ( A ^o B ) .o ( A ^o C ) ) )

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
    cC
    coa
    co
    #
    coe
    co
    #
    cA
    cB
    coe
    co
    #
    cA
    cC
    coe
    co
    #
    comu
    co
    #
    wceq
    #
    @1
    @2
    wa
    #
    @8
    cA
    cA
    c0
    wceq
    #
    @9
    @8
    @9
    @8
    @10
    c0
    @3
    coe
    co
    #
    c0
    cB
    coe
    co
    #
    c0
    cC
    coe
    co
    #
    comu
    co
    #
    wceq
    #
    @9
    cB
    c0
    wceq
    #
    cC
    c0
    wceq
    #
    wa
    #
    @15
    @9
    @18
    wa
    #
    @11
    c0
    c0
    coe
    co
    #
    @14
    @19
    @3
    c0
    c0
    coe
    @9
    @3
    c0
    wceq
    @18
    cB
    cC
    oa00
    #
    biimpar
    oveq2d
    @18
    @14
    @20
    wceq
    @9
    @18
    @14
    @20
    c1o
    comu
    co
    #
    @20
    @16
    @17
    @12
    @20
    @13
    c1o
    comu
    cB
    c0
    c0
    coe
    oveq2
    @17
    @13
    @20
    c1o
    cC
    c0
    c0
    coe
    oveq2
    oe0m0
    syl6eq
    oveqan12d
    @20
    con0
    wcel
    #
    @22
    @20
    wceq
    c0
    con0
    wcel
    #
    @24
    @23
    0elon
    0elon
    c0
    c0
    oecl
    mp2an
    @20
    om1
    ax-mp
    syl6eq
    adantl
    eqtr4d
    @9
    @18
    wn
    #
    wa
    @11
    c0
    @14
    @9
    @11
    c0
    wceq
    #
    @25
    @9
    c0
    @3
    wcel
    #
    @3
    c0
    wne
    #
    @26
    @25
    @9
    @3
    con0
    wcel
    #
    @27
    @28
    wb
    cB
    cC
    oacl
    #
    @3
    on0eln0
    syl
    @9
    @29
    @27
    @26
    wb
    @30
    @3
    oe0m1
    syl
    @9
    @18
    @3
    c0
    @21
    necon3abid
    3bitr3d
    biimpar
    @9
    @25
    @14
    c0
    wceq
    #
    @9
    @25
    c0
    cB
    wcel
    #
    c0
    cC
    wcel
    #
    wo
    #
    @31
    @9
    @34
    cB
    c0
    wne
    #
    cC
    c0
    wne
    #
    wo
    @25
    @9
    @32
    @35
    @33
    @36
    @1
    @32
    @35
    wb
    @2
    cB
    on0eln0
    adantr
    @2
    @33
    @36
    wb
    @1
    cC
    on0eln0
    adantl
    orbi12d
    cB
    c0
    cC
    c0
    neorian
    syl6bb
    @9
    @34
    @31
    @9
    @32
    @31
    @33
    @1
    @32
    @2
    @31
    @1
    @32
    wa
    #
    @2
    @14
    c0
    @13
    comu
    co
    #
    c0
    @37
    @12
    c0
    @13
    comu
    @1
    @32
    @12
    c0
    wceq
    cB
    oe0m1
    biimpa
    oveq1d
    @2
    @13
    con0
    wcel
    #
    @38
    c0
    wceq
    @24
    @2
    @39
    0elon
    c0
    cC
    oecl
    mpan
    @13
    om0r
    syl
    sylan9eq
    an32s
    @1
    @2
    @33
    @31
    @2
    @33
    wa
    #
    @1
    @14
    @12
    c0
    comu
    co
    #
    c0
    @40
    @13
    c0
    @12
    comu
    @2
    @33
    @13
    c0
    wceq
    cC
    oe0m1
    biimpa
    oveq2d
    @1
    @12
    con0
    wcel
    #
    @41
    c0
    wceq
    @24
    @1
    @42
    0elon
    c0
    cB
    oecl
    mpan
    @12
    om0
    syl
    sylan9eqr
    anassrs
    jaodan
    ex
    sylbird
    imp
    eqtr4d
    pm2.61dan
    @10
    @4
    @11
    @7
    @14
    cA
    c0
    @3
    coe
    oveq1
    @10
    @5
    @12
    @6
    @13
    comu
    cA
    c0
    cB
    coe
    oveq1
    cA
    c0
    cC
    coe
    oveq1
    oveq12d
    eqeq12d
    syl5ibr
    impcom
    @0
    c0
    cA
    wcel
    #
    @9
    @8
    @0
    @43
    wa
    #
    @1
    @2
    @8
    @44
    @1
    @2
    @8
    wi
    @2
    @44
    cA
    c1o
    cif
    #
    @3
    coe
    co
    #
    @45
    cB
    coe
    co
    #
    @45
    cC
    coe
    co
    #
    comu
    co
    #
    wceq
    #
    wi
    @2
    @45
    @1
    cB
    c1o
    cif
    #
    cC
    coa
    co
    #
    coe
    co
    #
    @45
    @51
    coe
    co
    #
    @48
    comu
    co
    #
    wceq
    #
    wi
    cA
    cB
    c1o
    c1o
    cA
    @45
    wceq
    #
    @8
    @50
    @2
    @57
    @4
    @46
    @7
    @49
    cA
    @45
    @3
    coe
    oveq1
    @57
    @5
    @47
    @6
    @48
    comu
    cA
    @45
    cB
    coe
    oveq1
    cA
    @45
    cC
    coe
    oveq1
    oveq12d
    eqeq12d
    imbi2d
    cB
    @51
    wceq
    #
    @50
    @56
    @2
    @58
    @46
    @53
    @49
    @55
    @58
    @3
    @52
    @45
    coe
    cB
    @51
    cC
    coa
    oveq1
    oveq2d
    @58
    @47
    @54
    @48
    comu
    cB
    @51
    @45
    coe
    oveq2
    oveq1d
    eqeq12d
    imbi2d
    @45
    @51
    cC
    @45
    con0
    wcel
    #
    c0
    @45
    wcel
    #
    @44
    @59
    @60
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
    @57
    @0
    @59
    @43
    @60
    cA
    @45
    con0
    eleq1
    cA
    @45
    c0
    eleq2
    anbi12d
    c1o
    @45
    wceq
    @61
    @59
    @62
    @60
    c1o
    @45
    con0
    eleq1
    c1o
    @45
    c0
    eleq2
    anbi12d
    @61
    @62
    1on
    0lt1o
    pm3.2i
    elimhyp
    #
    simpli
    @59
    @60
    @63
    simpri
    cB
    c1o
    con0
    1on
    elimel
    oeoalem
    dedth2h
    impr
    an32s
    oe0lem
    3impb
end
