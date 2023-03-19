include "con0.mm"
include "wcel.mm"
include "wss.mm"
include "comu.mm"
include "co.mm"
include "wi.mm"
include "wa.mm"
include "cv.mm"
include "c0.mm"
include "csuc.mm"
include "wceq.mm"
include "oveq2.mm"
include "sseq12d.mm"
include "om0.mm"
include "0ss.mm"
include "syl6eqss.mm"
include "ad2antrr.mm"
include "w3a.mm"
include "coa.mm"
include "omcl.mm"
include "3adant2.mm"
include "3adant1.mm"
include "simp1.mm"
include "oawordri.mm"
include "syl3anc.mm"
include "imp.mm"
include "adantrl.mm"
include "wb.mm"
include "oaword.mm"
include "syld3an3.mm"
include "biimpa.mm"
include "adantrr.mm"
include "sstrd.mm"
include "omsuc.mm"
include "adantr.mm"
include "3sstr4d.mm"
include "exp520.mm"
include "com3r.mm"
include "imp4c.mm"
include "wlim.mm"
include "wral.mm"
include "cvv.mm"
include "vex.mm"
include "ciun.mm"
include "ss2iun.mm"
include "omlim.mm"
include "ad2ant2rl.mm"
include "adantl.mm"
include "syl5ibr.mm"
include "anandirs.mm"
include "mpanr1.mm"
include "expcom.mm"
include "adantrd.mm"
include "tfinds3.mm"
include "expd.mm"
include "3impib.mm"
include "3coml.mm"

theorem omwordri
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( A e. On /\ B e. On /\ C e. On ) -> ( A C_ B -> ( A .o C ) C_ ( B .o C ) ) )

  proof
    cC
    con0
    wcel
    #
    cA
    con0
    wcel
    #
    cB
    con0
    wcel
    #
    cA
    cB
    wss
    #
    cA
    cC
    comu
    co
    #
    cB
    cC
    comu
    co
    #
    wss
    #
    wi
    #
    @0
    @1
    @2
    @7
    @0
    @1
    @2
    wa
    #
    @3
    @6
    cA
    vx
    cv
    #
    comu
    co
    #
    cB
    @9
    comu
    co
    #
    wss
    #
    cA
    c0
    comu
    co
    #
    cB
    c0
    comu
    co
    #
    wss
    #
    cA
    vy
    cv
    #
    comu
    co
    #
    cB
    @16
    comu
    co
    #
    wss
    #
    cA
    @16
    csuc
    #
    comu
    co
    #
    cB
    @20
    comu
    co
    #
    wss
    #
    @6
    @8
    @3
    wa
    vx
    vy
    cC
    @9
    c0
    wceq
    @10
    @13
    @11
    @14
    @9
    c0
    cA
    comu
    oveq2
    @9
    c0
    cB
    comu
    oveq2
    sseq12d
    @9
    @16
    wceq
    @10
    @17
    @11
    @18
    @9
    @16
    cA
    comu
    oveq2
    @9
    @16
    cB
    comu
    oveq2
    sseq12d
    @9
    @20
    wceq
    @10
    @21
    @11
    @22
    @9
    @20
    cA
    comu
    oveq2
    @9
    @20
    cB
    comu
    oveq2
    sseq12d
    @9
    cC
    wceq
    @10
    @4
    @11
    @5
    @9
    cC
    cA
    comu
    oveq2
    @9
    cC
    cB
    comu
    oveq2
    sseq12d
    @1
    @15
    @2
    @3
    @1
    @13
    c0
    @14
    cA
    om0
    @14
    0ss
    syl6eqss
    ad2antrr
    @16
    con0
    wcel
    #
    @1
    @2
    @3
    @19
    @23
    wi
    #
    @1
    @2
    @24
    @3
    @25
    wi
    @1
    @2
    @24
    @3
    @19
    @23
    @1
    @2
    @24
    w3a
    #
    @3
    @19
    wa
    #
    wa
    #
    @17
    cA
    coa
    co
    #
    @18
    cB
    coa
    co
    #
    @21
    @22
    @28
    @29
    @18
    cA
    coa
    co
    #
    @30
    @26
    @19
    @29
    @31
    wss
    #
    @3
    @26
    @19
    @32
    @26
    @17
    con0
    wcel
    #
    @18
    con0
    wcel
    #
    @1
    @19
    @32
    wi
    @1
    @24
    @33
    @2
    cA
    @16
    omcl
    3adant2
    @2
    @24
    @34
    @1
    cB
    @16
    omcl
    3adant1
    #
    @1
    @2
    @24
    simp1
    @17
    @18
    cA
    oawordri
    syl3anc
    imp
    adantrl
    @26
    @3
    @31
    @30
    wss
    #
    @19
    @26
    @3
    @36
    @1
    @2
    @24
    @34
    @3
    @36
    wb
    @35
    cA
    cB
    @18
    oaword
    syld3an3
    biimpa
    adantrr
    sstrd
    @26
    @21
    @29
    wceq
    #
    @27
    @1
    @24
    @37
    @2
    cA
    @16
    omsuc
    3adant2
    adantr
    @26
    @22
    @30
    wceq
    #
    @27
    @2
    @24
    @38
    @1
    cB
    @16
    omsuc
    3adant1
    adantr
    3sstr4d
    exp520
    com3r
    imp4c
    @9
    wlim
    #
    @8
    @19
    vy
    @9
    wral
    #
    @12
    wi
    #
    @3
    @8
    @39
    @41
    @8
    @9
    cvv
    wcel
    #
    @39
    @41
    vx
    vex
    @1
    @2
    @42
    @39
    wa
    #
    @41
    @40
    @12
    @1
    @43
    wa
    #
    @2
    @43
    wa
    #
    wa
    #
    vy
    @9
    @17
    ciun
    #
    vy
    @9
    @18
    ciun
    #
    wss
    vy
    @9
    @17
    @18
    ss2iun
    @46
    @10
    @47
    @11
    @48
    @1
    @43
    @10
    @47
    wceq
    @43
    @2
    vy
    cA
    @9
    cvv
    omlim
    ad2ant2rl
    @45
    @11
    @48
    wceq
    @44
    vy
    cB
    @9
    cvv
    omlim
    adantl
    sseq12d
    syl5ibr
    anandirs
    mpanr1
    expcom
    adantrd
    tfinds3
    expd
    3impib
    3coml
end
