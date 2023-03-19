include "cn0.mm"
include "wcel.mm"
include "cz.mm"
include "w3a.mm"
include "cgcd.mm"
include "co.mm"
include "c1.mm"
include "wceq.mm"
include "c2.mm"
include "cexp.mm"
include "cmul.mm"
include "nn0z.mm"
include "gcdcl.mm"
include "syl2an.mm"
include "3adant2.mm"
include "3ad2ant1.mm"
include "nn0cnd.mm"
include "sqvald.mm"
include "simp13.mm"
include "cc.mm"
include "nn0cn.mm"
include "mulcomd.mm"
include "wa.mm"
include "simpl3.mm"
include "eqeq1d.mm"
include "biimp3a.mm"
include "oveq12d.mm"
include "simp11.mm"
include "nn0zd.mm"
include "mulgcd.mm"
include "syl3anc.mm"
include "simp12.mm"
include "3eqtr3d.mm"
include "oveq2d.mm"
include "mulgcdr.mm"
include "sylan.mm"
include "ancoms.mm"
include "3adant1.mm"
include "cabs.mm"
include "cfv.mm"
include "3ad2ant3.mm"
include "gcdid.mm"
include "syl.mm"
include "oveq1d.mm"
include "simp2.mm"
include "gcdabs1.mm"
include "syl2anc.mm"
include "eqtrd.mm"
include "gcdass.mm"
include "gcdcom.mm"
include "3eqtr4d.mm"
include "biimpar.mm"
include "3adant3.mm"
include "mulid1d.mm"
include "3eqtrrd.mm"
include "3expia.mm"

theorem coprimeprodsq
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( ( A e. NN0 /\ B e. ZZ /\ C e. NN0 ) /\ ( ( A gcd B ) gcd C ) = 1 ) -> ( ( C ^ 2 ) = ( A x. B ) -> A = ( ( A gcd C ) ^ 2 ) ) )

  proof
    cA
    cn0
    wcel
    #
    cB
    cz
    wcel
    #
    cC
    cn0
    wcel
    #
    w3a
    #
    cA
    cB
    cgcd
    co
    cC
    cgcd
    co
    #
    c1
    wceq
    #
    cC
    c2
    cexp
    co
    #
    cA
    cB
    cmul
    co
    #
    wceq
    #
    cA
    cA
    cC
    cgcd
    co
    #
    c2
    cexp
    co
    #
    wceq
    @3
    @5
    @8
    w3a
    #
    @10
    @9
    @9
    cmul
    co
    #
    cA
    @9
    cC
    cB
    cgcd
    co
    #
    cgcd
    co
    #
    cmul
    co
    #
    cA
    @11
    @9
    @11
    @9
    @3
    @5
    @9
    cn0
    wcel
    #
    @8
    @0
    @2
    @16
    @1
    @0
    cA
    cz
    wcel
    #
    cC
    cz
    wcel
    #
    @16
    @2
    cA
    nn0z
    #
    cC
    nn0z
    #
    cA
    cC
    gcdcl
    syl2an
    3adant2
    3ad2ant1
    #
    nn0cnd
    sqvald
    @11
    cA
    @9
    cmul
    co
    #
    cC
    @9
    cmul
    co
    #
    cgcd
    co
    #
    @22
    cA
    @13
    cmul
    co
    #
    cgcd
    co
    #
    @12
    @15
    @11
    @23
    @25
    @22
    cgcd
    @11
    cC
    cA
    cmul
    co
    #
    cC
    cC
    cmul
    co
    #
    cgcd
    co
    #
    cA
    cC
    cmul
    co
    #
    @7
    cgcd
    co
    #
    @23
    @25
    @11
    @27
    @30
    @28
    @7
    cgcd
    @11
    cC
    cA
    @11
    cC
    @0
    @1
    @2
    @5
    @8
    simp13
    #
    nn0cnd
    @3
    @5
    cA
    cc
    wcel
    #
    @8
    @0
    @1
    @33
    @2
    cA
    nn0cn
    3ad2ant1
    3ad2ant1
    #
    mulcomd
    @3
    @5
    @8
    @28
    @7
    wceq
    @3
    @5
    wa
    #
    @6
    @28
    @7
    @35
    cC
    @35
    cC
    @0
    @1
    @2
    @5
    simpl3
    nn0cnd
    sqvald
    eqeq1d
    biimp3a
    oveq12d
    @11
    @2
    @17
    @18
    @29
    @23
    wceq
    @32
    @11
    cA
    @0
    @1
    @2
    @5
    @8
    simp11
    #
    nn0zd
    #
    @11
    cC
    @32
    nn0zd
    #
    cC
    cA
    cC
    mulgcd
    syl3anc
    @11
    @0
    @18
    @1
    @31
    @25
    wceq
    @36
    @38
    @0
    @1
    @2
    @5
    @8
    simp12
    cA
    cC
    cB
    mulgcd
    syl3anc
    3eqtr3d
    oveq2d
    @11
    @17
    @18
    @16
    @24
    @12
    wceq
    @37
    @38
    @21
    cA
    cC
    @9
    mulgcdr
    syl3anc
    @11
    @0
    @9
    cz
    wcel
    @13
    cz
    wcel
    #
    @26
    @15
    wceq
    @36
    @11
    @9
    @21
    nn0zd
    @11
    @13
    @3
    @5
    @13
    cn0
    wcel
    #
    @8
    @1
    @2
    @40
    @0
    @2
    @1
    @40
    @2
    @18
    @1
    @40
    @20
    cC
    cB
    gcdcl
    sylan
    ancoms
    3adant1
    #
    3ad2ant1
    nn0zd
    cA
    @9
    @13
    mulgcd
    syl3anc
    3eqtr3d
    @11
    @15
    cA
    c1
    cmul
    co
    #
    cA
    @3
    @5
    @15
    @42
    wceq
    @8
    @35
    @14
    c1
    cA
    cmul
    @3
    @14
    c1
    wceq
    @5
    @3
    @14
    @4
    c1
    @3
    cA
    cC
    @13
    cgcd
    co
    #
    cgcd
    co
    #
    cA
    cB
    cC
    cgcd
    co
    #
    cgcd
    co
    #
    @14
    @4
    @3
    @43
    @45
    cA
    cgcd
    @3
    cC
    cC
    cgcd
    co
    #
    cB
    cgcd
    co
    #
    @13
    @43
    @45
    @3
    @48
    cC
    cabs
    cfv
    #
    cB
    cgcd
    co
    #
    @13
    @3
    @47
    @49
    cB
    cgcd
    @3
    @18
    @47
    @49
    wceq
    @2
    @0
    @18
    @1
    @20
    3ad2ant3
    #
    cC
    gcdid
    syl
    oveq1d
    @3
    @18
    @1
    @50
    @13
    wceq
    @51
    @0
    @1
    @2
    simp2
    #
    cB
    cC
    gcdabs1
    syl2anc
    eqtrd
    @3
    @18
    @18
    @1
    @48
    @43
    wceq
    @51
    @51
    @52
    cB
    cC
    cC
    gcdass
    syl3anc
    @3
    @18
    @1
    @13
    @45
    wceq
    @51
    @52
    cC
    cB
    gcdcom
    syl2anc
    3eqtr3d
    oveq2d
    @3
    @17
    @18
    @39
    @14
    @44
    wceq
    @0
    @1
    @17
    @2
    @19
    3ad2ant1
    #
    @51
    @3
    @13
    @41
    nn0zd
    @13
    cC
    cA
    gcdass
    syl3anc
    @3
    @17
    @1
    @18
    @4
    @46
    wceq
    @53
    @52
    @51
    cC
    cB
    cA
    gcdass
    syl3anc
    3eqtr4d
    eqeq1d
    biimpar
    oveq2d
    3adant3
    @11
    cA
    @34
    mulid1d
    eqtrd
    3eqtrrd
    3expia
end
