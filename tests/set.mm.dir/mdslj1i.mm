include "cmd.mm"
include "wbr.mm"
include "cdmd.mm"
include "wa.mm"
include "cin.mm"
include "wss.mm"
include "chj.mm"
include "co.mm"
include "ssin.mm"
include "bicomi.mm"
include "chjcli.mm"
include "chlubi.mm"
include "anbi12i.mm"
include "w3a.mm"
include "wceq.mm"
include "simpr.mm"
include "simpl.mm"
include "cch.mm"
include "wcel.mm"
include "3pm3.2i.mm"
include "dmdsl3.mm"
include "mpan.mm"
include "syl3an.mm"
include "chincli.mm"
include "chub1i.mm"
include "chlej1i.mm"
include "mp1i.mm"
include "eqsstr3d.mm"
include "chub2i.mm"
include "jca.mm"
include "sylib.mm"
include "ssrin.mm"
include "syl.mm"
include "syl6ss.mm"
include "adantr.mm"
include "inss2.mm"
include "mpbir2an.mm"
include "a1i.mm"
include "mdsl3.mm"
include "sseqtrd.mm"
include "3expb.mm"
include "sylan2b.mm"
include "lediri.mm"
include "eqssd.mm"

theorem mdslj1i
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume mdslle1.1: |- A e. CH
  assume mdslle1.2: |- B e. CH
  assume mdslle1.3: |- C e. CH
  assume mdslle1.4: |- D e. CH


  assert |- ( ( ( A MH B /\ B MH* A ) /\ ( A C_ ( C i^i D ) /\ ( C vH D ) C_ ( A vH B ) ) ) -> ( ( C vH D ) i^i B ) = ( ( C i^i B ) vH ( D i^i B ) ) )

  proof
    cA
    cB
    cmd
    wbr
    #
    cB
    cA
    cdmd
    wbr
    #
    wa
    #
    cA
    cC
    cD
    cin
    wss
    #
    cC
    cD
    chj
    co
    #
    cA
    cB
    chj
    co
    #
    wss
    #
    wa
    #
    wa
    #
    @4
    cB
    cin
    #
    cC
    cB
    cin
    #
    cD
    cB
    cin
    #
    chj
    co
    #
    @7
    @2
    cA
    cC
    wss
    #
    cA
    cD
    wss
    #
    wa
    #
    cC
    @5
    wss
    #
    cD
    @5
    wss
    #
    wa
    #
    wa
    @9
    @12
    wss
    #
    @3
    @15
    @6
    @18
    @15
    @3
    cA
    cC
    cD
    ssin
    bicomi
    @18
    @6
    cC
    cD
    @5
    mdslle1.3
    mdslle1.4
    cA
    cB
    mdslle1.1
    mdslle1.2
    chjcli
    chlubi
    bicomi
    anbi12i
    @2
    @15
    @18
    @19
    @2
    @15
    @18
    w3a
    #
    @9
    @12
    cA
    chj
    co
    #
    cB
    cin
    #
    @12
    @20
    @4
    @21
    wss
    #
    @9
    @22
    wss
    @20
    cC
    @21
    wss
    #
    cD
    @21
    wss
    #
    wa
    @23
    @20
    @24
    @25
    @20
    cC
    @10
    cA
    chj
    co
    #
    @21
    @2
    @1
    @15
    @13
    @18
    @16
    @26
    cC
    wceq
    #
    @0
    @1
    simpr
    #
    @13
    @14
    simpl
    @16
    @17
    simpl
    cA
    cch
    wcel
    #
    cB
    cch
    wcel
    #
    cC
    cch
    wcel
    #
    w3a
    @1
    @13
    @16
    w3a
    @27
    @29
    @30
    @31
    mdslle1.1
    mdslle1.2
    mdslle1.3
    3pm3.2i
    cA
    cB
    cC
    dmdsl3
    mpan
    syl3an
    @10
    @12
    wss
    @26
    @21
    wss
    @20
    @10
    @11
    cC
    cB
    mdslle1.3
    mdslle1.2
    chincli
    #
    cD
    cB
    mdslle1.4
    mdslle1.2
    chincli
    #
    chub1i
    #
    @10
    @12
    cA
    @32
    @10
    @11
    @32
    @33
    chjcli
    #
    mdslle1.1
    chlej1i
    mp1i
    eqsstr3d
    @20
    cD
    @11
    cA
    chj
    co
    #
    @21
    @2
    @1
    @15
    @14
    @18
    @17
    @36
    cD
    wceq
    #
    @28
    @13
    @14
    simpr
    @16
    @17
    simpr
    @29
    @30
    cD
    cch
    wcel
    #
    w3a
    @1
    @14
    @17
    w3a
    @37
    @29
    @30
    @38
    mdslle1.1
    mdslle1.2
    mdslle1.4
    3pm3.2i
    cA
    cB
    cD
    dmdsl3
    mpan
    syl3an
    @11
    @12
    wss
    @36
    @21
    wss
    @20
    @11
    @10
    @33
    @32
    chub2i
    @11
    @12
    cA
    @33
    @35
    mdslle1.1
    chlej1i
    mp1i
    eqsstr3d
    jca
    cC
    cD
    @21
    mdslle1.3
    mdslle1.4
    @12
    cA
    @35
    mdslle1.1
    chjcli
    chlubi
    sylib
    @4
    @21
    cB
    ssrin
    syl
    @2
    @0
    @15
    cA
    cB
    cin
    #
    @12
    wss
    #
    @18
    @12
    cB
    wss
    #
    @22
    @12
    wceq
    #
    @0
    @1
    simpl
    @13
    @40
    @14
    @13
    @39
    @10
    @12
    cA
    cC
    cB
    ssrin
    @34
    syl6ss
    adantr
    @41
    @18
    @41
    @10
    cB
    wss
    #
    @11
    cB
    wss
    #
    cC
    cB
    inss2
    cD
    cB
    inss2
    @43
    @44
    wa
    @41
    @10
    @11
    cB
    @32
    @33
    mdslle1.2
    chlubi
    bicomi
    mpbir2an
    a1i
    @29
    @30
    @12
    cch
    wcel
    #
    w3a
    @0
    @40
    @41
    w3a
    @42
    @29
    @30
    @45
    mdslle1.1
    mdslle1.2
    @35
    3pm3.2i
    cA
    cB
    @12
    mdsl3
    mpan
    syl3an
    sseqtrd
    3expb
    sylan2b
    @12
    @9
    wss
    @8
    cC
    cD
    cB
    mdslle1.3
    mdslle1.4
    mdslle1.2
    lediri
    a1i
    eqssd
end
