include "cmd.mm"
include "wbr.mm"
include "cdmd.mm"
include "wa.mm"
include "cin.mm"
include "wss.mm"
include "chj.mm"
include "co.mm"
include "lejdiri.mm"
include "a1i.mm"
include "ssin.mm"
include "bicomi.mm"
include "chlubi.mm"
include "anbi12i.mm"
include "w3a.mm"
include "wceq.mm"
include "simpr.mm"
include "chub2i.mm"
include "ssini.mm"
include "chlej1i.mm"
include "chjcomi.mm"
include "syl6sseq.mm"
include "ssinss1.mm"
include "syl.mm"
include "adantr.mm"
include "cch.mm"
include "wcel.mm"
include "chjcli.mm"
include "chincli.mm"
include "3pm3.2i.mm"
include "dmdsl3.mm"
include "mpan.mm"
include "syl3an.mm"
include "inss1.mm"
include "ssrin.mm"
include "ax-mp.mm"
include "simpl.mm"
include "mdsl3.mm"
include "syl5sseq.mm"
include "inss2.mm"
include "ssind.mm"
include "eqsstr3d.mm"
include "3expb.mm"
include "sylan2b.mm"
include "eqssd.mm"

theorem mdslj2i
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume mdslle1.1: |- A e. CH
  assume mdslle1.2: |- B e. CH
  assume mdslle1.3: |- C e. CH
  assume mdslle1.4: |- D e. CH


  assert |- ( ( ( A MH B /\ B MH* A ) /\ ( ( A i^i B ) C_ ( C i^i D ) /\ ( C vH D ) C_ B ) ) -> ( ( C i^i D ) vH A ) = ( ( C vH A ) i^i ( D vH A ) ) )

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
    cB
    cin
    #
    cC
    cD
    cin
    #
    wss
    #
    cC
    cD
    chj
    co
    cB
    wss
    #
    wa
    #
    wa
    #
    @4
    cA
    chj
    co
    #
    cC
    cA
    chj
    co
    #
    cD
    cA
    chj
    co
    #
    cin
    #
    @9
    @12
    wss
    @8
    cC
    cD
    cA
    mdslle1.3
    mdslle1.4
    mdslle1.1
    lejdiri
    a1i
    @7
    @2
    @3
    cC
    wss
    #
    @3
    cD
    wss
    #
    wa
    #
    cC
    cB
    wss
    #
    cD
    cB
    wss
    #
    wa
    #
    wa
    @12
    @9
    wss
    #
    @5
    @15
    @6
    @18
    @15
    @5
    @3
    cC
    cD
    ssin
    bicomi
    @18
    @6
    cC
    cD
    cB
    mdslle1.3
    mdslle1.4
    mdslle1.2
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
    @12
    @12
    cB
    cin
    #
    cA
    chj
    co
    #
    @9
    @2
    @1
    @15
    cA
    @12
    wss
    #
    @18
    @12
    cA
    cB
    chj
    co
    #
    wss
    #
    @22
    @12
    wceq
    #
    @0
    @1
    simpr
    @23
    @15
    cA
    @10
    @11
    cA
    cC
    mdslle1.1
    mdslle1.3
    chub2i
    cA
    cD
    mdslle1.1
    mdslle1.4
    chub2i
    ssini
    a1i
    @16
    @25
    @17
    @16
    @10
    @24
    wss
    @25
    @16
    @10
    cB
    cA
    chj
    co
    @24
    cC
    cB
    cA
    mdslle1.3
    mdslle1.2
    mdslle1.1
    chlej1i
    cB
    cA
    mdslle1.2
    mdslle1.1
    chjcomi
    syl6sseq
    @10
    @11
    @24
    ssinss1
    syl
    adantr
    cA
    cch
    wcel
    #
    cB
    cch
    wcel
    #
    @12
    cch
    wcel
    #
    w3a
    @1
    @23
    @25
    w3a
    @26
    @27
    @28
    @29
    mdslle1.1
    mdslle1.2
    @10
    @11
    cC
    cA
    mdslle1.3
    mdslle1.1
    chjcli
    cD
    cA
    mdslle1.4
    mdslle1.1
    chjcli
    chincli
    #
    3pm3.2i
    cA
    cB
    @12
    dmdsl3
    mpan
    syl3an
    @20
    @21
    @4
    wss
    @22
    @9
    wss
    @20
    @21
    cC
    cD
    @20
    @10
    cB
    cin
    #
    @21
    cC
    @12
    @10
    wss
    @21
    @31
    wss
    @10
    @11
    inss1
    @12
    @10
    cB
    ssrin
    ax-mp
    @2
    @0
    @15
    @13
    @18
    @16
    @31
    cC
    wceq
    #
    @0
    @1
    simpl
    #
    @13
    @14
    simpl
    @16
    @17
    simpl
    @27
    @28
    cC
    cch
    wcel
    #
    w3a
    @0
    @13
    @16
    w3a
    @32
    @27
    @28
    @34
    mdslle1.1
    mdslle1.2
    mdslle1.3
    3pm3.2i
    cA
    cB
    cC
    mdsl3
    mpan
    syl3an
    syl5sseq
    @20
    @11
    cB
    cin
    #
    @21
    cD
    @12
    @11
    wss
    @21
    @35
    wss
    @10
    @11
    inss2
    @12
    @11
    cB
    ssrin
    ax-mp
    @2
    @0
    @15
    @14
    @18
    @17
    @35
    cD
    wceq
    #
    @33
    @13
    @14
    simpr
    @16
    @17
    simpr
    @27
    @28
    cD
    cch
    wcel
    #
    w3a
    @0
    @14
    @17
    w3a
    @36
    @27
    @28
    @37
    mdslle1.1
    mdslle1.2
    mdslle1.4
    3pm3.2i
    cA
    cB
    cD
    mdsl3
    mpan
    syl3an
    syl5sseq
    ssind
    @21
    @4
    cA
    @12
    cB
    @30
    mdslle1.2
    chincli
    cC
    cD
    mdslle1.3
    mdslle1.4
    chincli
    mdslle1.1
    chlej1i
    syl
    eqsstr3d
    3expb
    sylan2b
    eqssd
end
