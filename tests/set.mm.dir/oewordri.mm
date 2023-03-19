include "con0.mm"
include "wcel.mm"
include "coe.mm"
include "co.mm"
include "wss.mm"
include "wi.mm"
include "cv.mm"
include "c0.mm"
include "csuc.mm"
include "wa.mm"
include "wceq.mm"
include "oveq2.mm"
include "sseq12d.mm"
include "c1o.mm"
include "onelon.mm"
include "oe0.mm"
include "syl.mm"
include "adantr.mm"
include "eqtr4d.mm"
include "eqimss.mm"
include "simpl.mm"
include "onelss.mm"
include "imp.mm"
include "jca31.mm"
include "w3a.mm"
include "comu.mm"
include "oecl.mm"
include "3adant2.mm"
include "3adant1.mm"
include "simp1.mm"
include "omwordri.mm"
include "syl3anc.mm"
include "adantrl.mm"
include "omwordi.mm"
include "syld3an3.mm"
include "adantrr.mm"
include "sstrd.mm"
include "oesuc.mm"
include "3sstr4d.mm"
include "exp520.mm"
include "com3r.mm"
include "imp4c.mm"
include "syl5.mm"
include "wlim.mm"
include "wral.mm"
include "cvv.mm"
include "vex.mm"
include "limelon.mm"
include "mpan.mm"
include "0ellim.mm"
include "oe0m1.mm"
include "biimpa.mm"
include "syl2anc.mm"
include "0ss.mm"
include "syl6eqss.mm"
include "oveq1.mm"
include "sseq1d.mm"
include "syl5ibr.mm"
include "adantl.mm"
include "a1dd.mm"
include "ciun.mm"
include "ss2iun.mm"
include "oelim.mm"
include "mpanlr1.mm"
include "an32s.mm"
include "adantllr.mm"
include "anim1i.mm"
include "wne.mm"
include "ne0i.mm"
include "on0eln0.mm"
include "adantlr.mm"
include "adantlll.mm"
include "ex.mm"
include "oe0lem.mm"
include "ancri.mm"
include "syl11.mm"
include "tfinds3.mm"
include "expd.mm"
include "impcom.mm"

theorem oewordri
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( B e. On /\ C e. On ) -> ( A e. B -> ( A ^o C ) C_ ( B ^o C ) ) )

  proof
    cC
    con0
    wcel
    #
    cB
    con0
    wcel
    #
    cA
    cB
    wcel
    #
    cA
    cC
    coe
    co
    #
    cB
    cC
    coe
    co
    #
    wss
    #
    wi
    @0
    @1
    @2
    @5
    cA
    vx
    cv
    #
    coe
    co
    #
    cB
    @6
    coe
    co
    #
    wss
    #
    cA
    c0
    coe
    co
    #
    cB
    c0
    coe
    co
    #
    wss
    #
    cA
    vy
    cv
    #
    coe
    co
    #
    cB
    @13
    coe
    co
    #
    wss
    #
    cA
    @13
    csuc
    #
    coe
    co
    #
    cB
    @17
    coe
    co
    #
    wss
    #
    @5
    @1
    @2
    wa
    #
    vx
    vy
    cC
    @6
    c0
    wceq
    @7
    @10
    @8
    @11
    @6
    c0
    cA
    coe
    oveq2
    @6
    c0
    cB
    coe
    oveq2
    sseq12d
    @6
    @13
    wceq
    @7
    @14
    @8
    @15
    @6
    @13
    cA
    coe
    oveq2
    @6
    @13
    cB
    coe
    oveq2
    sseq12d
    @6
    @17
    wceq
    @7
    @18
    @8
    @19
    @6
    @17
    cA
    coe
    oveq2
    @6
    @17
    cB
    coe
    oveq2
    sseq12d
    @6
    cC
    wceq
    @7
    @3
    @8
    @4
    @6
    cC
    cA
    coe
    oveq2
    @6
    cC
    cB
    coe
    oveq2
    sseq12d
    @21
    @10
    @11
    wceq
    @12
    @21
    @10
    c1o
    @11
    @21
    cA
    con0
    wcel
    #
    @10
    c1o
    wceq
    cB
    cA
    onelon
    #
    cA
    oe0
    syl
    @1
    @11
    c1o
    wceq
    @2
    cB
    oe0
    adantr
    eqtr4d
    @10
    @11
    eqimss
    syl
    @21
    @22
    @1
    wa
    cA
    cB
    wss
    #
    wa
    @13
    con0
    wcel
    #
    @16
    @20
    wi
    #
    @21
    @22
    @1
    @24
    @23
    @1
    @2
    simpl
    #
    @1
    @2
    @24
    cB
    cA
    onelss
    imp
    jca31
    @25
    @22
    @1
    @24
    @26
    @22
    @1
    @25
    @24
    @26
    wi
    @22
    @1
    @25
    @24
    @16
    @20
    @22
    @1
    @25
    w3a
    #
    @24
    @16
    wa
    #
    wa
    #
    @14
    cA
    comu
    co
    #
    @15
    cB
    comu
    co
    #
    @18
    @19
    @30
    @31
    @15
    cA
    comu
    co
    #
    @32
    @28
    @16
    @31
    @33
    wss
    #
    @24
    @28
    @16
    @34
    @28
    @14
    con0
    wcel
    #
    @15
    con0
    wcel
    #
    @22
    @16
    @34
    wi
    @22
    @25
    @35
    @1
    cA
    @13
    oecl
    3adant2
    @1
    @25
    @36
    @22
    cB
    @13
    oecl
    3adant1
    #
    @22
    @1
    @25
    simp1
    @14
    @15
    cA
    omwordri
    syl3anc
    imp
    adantrl
    @28
    @24
    @33
    @32
    wss
    #
    @16
    @28
    @24
    @38
    @22
    @1
    @25
    @36
    @24
    @38
    wi
    @37
    cA
    cB
    @15
    omwordi
    syld3an3
    imp
    adantrr
    sstrd
    @28
    @18
    @31
    wceq
    #
    @29
    @22
    @25
    @39
    @1
    cA
    @13
    oesuc
    3adant2
    adantr
    @28
    @19
    @32
    wceq
    #
    @29
    @1
    @25
    @40
    @22
    cB
    @13
    oesuc
    3adant1
    adantr
    3sstr4d
    exp520
    com3r
    imp4c
    syl5
    @22
    @21
    wa
    #
    @6
    wlim
    #
    @16
    vy
    @6
    wral
    #
    @9
    wi
    #
    @21
    @21
    @42
    @44
    wi
    cA
    @21
    cA
    c0
    wceq
    #
    wa
    @42
    @9
    @43
    @45
    @42
    @9
    wi
    @21
    @42
    @9
    @45
    c0
    @6
    coe
    co
    #
    @8
    wss
    @42
    @46
    c0
    @8
    @42
    @6
    con0
    wcel
    #
    c0
    @6
    wcel
    #
    @46
    c0
    wceq
    #
    @6
    cvv
    wcel
    #
    @42
    @47
    vx
    vex
    #
    @6
    cvv
    limelon
    mpan
    @6
    0ellim
    @47
    @48
    @49
    @6
    oe0m1
    biimpa
    syl2anc
    @8
    0ss
    syl6eqss
    @45
    @7
    @46
    @8
    cA
    c0
    @6
    coe
    oveq1
    sseq1d
    syl5ibr
    adantl
    a1dd
    @41
    c0
    cA
    wcel
    #
    wa
    #
    @42
    @44
    @43
    @9
    @53
    @42
    wa
    #
    vy
    @6
    @14
    ciun
    #
    vy
    @6
    @15
    ciun
    #
    wss
    vy
    @6
    @14
    @15
    ss2iun
    @54
    @7
    @55
    @8
    @56
    @22
    @52
    @42
    @7
    @55
    wceq
    #
    @21
    @22
    @42
    @52
    @57
    @22
    @50
    @42
    @52
    @57
    @51
    vy
    cA
    @6
    cvv
    oelim
    mpanlr1
    an32s
    adantllr
    @21
    @52
    @42
    @8
    @56
    wceq
    #
    @22
    @21
    @42
    @58
    @52
    @21
    @42
    wa
    @1
    @42
    wa
    c0
    cB
    wcel
    #
    @58
    @21
    @1
    @42
    @27
    anim1i
    @21
    @59
    @42
    @1
    @2
    @59
    @2
    @59
    @1
    cB
    c0
    wne
    cB
    cA
    ne0i
    cB
    on0eln0
    syl5ibr
    imp
    adantr
    @1
    @50
    @42
    @59
    @58
    @51
    vy
    cB
    @6
    cvv
    oelim
    mpanlr1
    syl2anc
    adantlr
    adantlll
    sseq12d
    syl5ibr
    ex
    oe0lem
    @21
    @22
    @23
    ancri
    syl11
    tfinds3
    expd
    impcom
end
