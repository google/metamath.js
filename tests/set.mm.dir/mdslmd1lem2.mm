include "cin.mm"
include "wss.mm"
include "chj.mm"
include "co.mm"
include "wi.mm"
include "wa.mm"
include "cmd.mm"
include "wbr.mm"
include "cdmd.mm"
include "ssrin.mm"
include "adantl.mm"
include "imim1i.mm"
include "wb.mm"
include "simpllr.mm"
include "chub2i.mm"
include "sstr.mm"
include "mpan2.mm"
include "ad2antrr.mm"
include "ad2antlr.mm"
include "simplr.mm"
include "ssind.mm"
include "ssin.mm"
include "chincli.mm"
include "sylbi.mm"
include "adantr.mm"
include "inss2.mm"
include "mpan.mm"
include "ad2antll.mm"
include "ancoms.mm"
include "ad2ant2l.mm"
include "adantll.mm"
include "ssinss1.mm"
include "ad2antrl.mm"
include "jca.mm"
include "chjcli.mm"
include "chlubi.mm"
include "sylib.mm"
include "mdslle1i.mm"
include "syl3anc.mm"
include "inindir.mm"
include "wceq.mm"
include "sylanb.mm"
include "ad2ant2r.mm"
include "simplll.mm"
include "simplrl.mm"
include "mdslj1i.mm"
include "sylan2.mm"
include "anassrs.mm"
include "ineq1d.mm"
include "syl5req.mm"
include "biimpi.mm"
include "anim12i.mm"
include "an4s.mm"
include "a1i.mm"
include "oveq2d.mm"
include "eqtr2d.mm"
include "sseq12d.mm"
include "bitr4d.mm"
include "exbiri.mm"
include "a2d.mm"
include "syl5.mm"

theorem mdslmd1lem2
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  let vx: setvar x
  let vy: setvar y
  assume mdslmd.1: |- A e. CH
  assume mdslmd.2: |- B e. CH
  assume mdslmd.3: |- C e. CH
  assume mdslmd.4: |- D e. CH
  assume mdslmd1lem.5: |- R e. CH


  assert |- ( ( ( A MH B /\ B MH* A ) /\ ( ( A C_ C /\ A C_ D ) /\ ( C C_ ( A vH B ) /\ D C_ ( A vH B ) ) ) ) -> ( ( ( R i^i B ) C_ ( D i^i B ) -> ( ( ( R i^i B ) vH ( C i^i B ) ) i^i ( D i^i B ) ) C_ ( ( R i^i B ) vH ( ( C i^i B ) i^i ( D i^i B ) ) ) ) -> ( ( ( C i^i D ) C_ R /\ R C_ D ) -> ( ( R vH C ) i^i D ) C_ ( R vH ( C i^i D ) ) ) ) )

  proof
    cR
    cB
    cin
    #
    cD
    cB
    cin
    #
    wss
    #
    @0
    cC
    cB
    cin
    #
    chj
    co
    #
    @1
    cin
    #
    @0
    @3
    @1
    cin
    #
    chj
    co
    #
    wss
    #
    wi
    cC
    cD
    cin
    #
    cR
    wss
    #
    cR
    cD
    wss
    #
    wa
    #
    @8
    wi
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
    wss
    #
    cA
    cD
    wss
    #
    wa
    #
    cC
    cA
    cB
    chj
    co
    #
    wss
    #
    cD
    @19
    wss
    #
    wa
    #
    wa
    #
    wa
    #
    @12
    cR
    cC
    chj
    co
    #
    cD
    cin
    #
    cR
    @9
    chj
    co
    #
    wss
    #
    wi
    @12
    @2
    @8
    @11
    @2
    @10
    cR
    cD
    cB
    ssrin
    adantl
    imim1i
    @24
    @12
    @8
    @28
    @24
    @12
    @28
    @8
    @24
    @12
    wa
    #
    @28
    @26
    cB
    cin
    #
    @27
    cB
    cin
    #
    wss
    #
    @8
    @29
    @14
    cA
    @26
    @27
    cin
    wss
    @26
    @27
    chj
    co
    @19
    wss
    #
    @28
    @32
    wb
    @13
    @14
    @23
    @12
    simpllr
    @29
    cA
    @26
    @27
    @29
    cA
    @25
    cD
    @23
    cA
    @25
    wss
    #
    @15
    @12
    @16
    @34
    @17
    @22
    @16
    cC
    @25
    wss
    @34
    cC
    cR
    mdslmd.3
    mdslmd1lem.5
    chub2i
    cA
    cC
    @25
    sstr
    mpan2
    ad2antrr
    ad2antlr
    @23
    @17
    @15
    @12
    @16
    @17
    @22
    simplr
    ad2antlr
    ssind
    @23
    cA
    @27
    wss
    #
    @15
    @12
    @18
    @35
    @22
    @18
    cA
    @9
    wss
    #
    @35
    cA
    cC
    cD
    ssin
    #
    @36
    @9
    @27
    wss
    @35
    @9
    cR
    cC
    cD
    mdslmd.3
    mdslmd.4
    chincli
    #
    mdslmd1lem.5
    chub2i
    cA
    @9
    @27
    sstr
    mpan2
    sylbi
    adantr
    ad2antlr
    ssind
    @29
    @26
    @19
    wss
    #
    @27
    @19
    wss
    #
    wa
    @33
    @29
    @39
    @40
    @23
    @39
    @15
    @12
    @21
    @39
    @18
    @20
    @26
    cD
    wss
    @21
    @39
    @25
    cD
    inss2
    @26
    cD
    @19
    sstr
    mpan
    ad2antll
    ad2antlr
    @29
    cR
    @19
    wss
    #
    @9
    @19
    wss
    #
    wa
    #
    @40
    @29
    @41
    @42
    @23
    @12
    @41
    @15
    @22
    @12
    @41
    @18
    @21
    @11
    @41
    @20
    @10
    @11
    @21
    @41
    cR
    cD
    @19
    sstr
    ancoms
    #
    ad2ant2l
    adantll
    #
    adantll
    @23
    @42
    @15
    @12
    @20
    @42
    @18
    @21
    cC
    cD
    @19
    ssinss1
    #
    ad2antrl
    ad2antlr
    jca
    cR
    @9
    @19
    mdslmd1lem.5
    @38
    cA
    cB
    mdslmd.1
    mdslmd.2
    chjcli
    #
    chlubi
    #
    sylib
    jca
    @26
    @27
    @19
    @25
    cD
    cR
    cC
    mdslmd1lem.5
    mdslmd.3
    chjcli
    mdslmd.4
    chincli
    #
    cR
    @9
    mdslmd1lem.5
    @38
    chjcli
    #
    @47
    chlubi
    sylib
    cA
    cB
    @26
    @27
    mdslmd.1
    mdslmd.2
    @49
    @50
    mdslle1i
    syl3anc
    @29
    @5
    @30
    @7
    @31
    @29
    @30
    @25
    cB
    cin
    #
    @1
    cin
    @5
    @25
    cD
    cB
    inindir
    @29
    @51
    @4
    @1
    @15
    @23
    @12
    @51
    @4
    wceq
    #
    @23
    @12
    wa
    #
    @15
    cA
    cR
    cC
    cin
    wss
    #
    @25
    @19
    wss
    #
    wa
    @52
    @53
    @54
    @55
    @53
    cA
    cR
    cC
    @18
    @10
    cA
    cR
    wss
    #
    @22
    @11
    @18
    @36
    @10
    @56
    @37
    cA
    @9
    cR
    sstr
    sylanb
    #
    ad2ant2r
    @16
    @17
    @22
    @12
    simplll
    ssind
    @53
    @41
    @20
    wa
    @55
    @53
    @41
    @20
    @45
    @18
    @20
    @21
    @12
    simplrl
    jca
    cR
    cC
    @19
    mdslmd1lem.5
    mdslmd.3
    @47
    chlubi
    sylib
    jca
    cA
    cB
    cR
    cC
    mdslmd.1
    mdslmd.2
    mdslmd1lem.5
    mdslmd.3
    mdslj1i
    sylan2
    anassrs
    ineq1d
    syl5req
    @29
    @31
    @0
    @9
    cB
    cin
    #
    chj
    co
    #
    @7
    @15
    @23
    @12
    @31
    @59
    wceq
    #
    @53
    @15
    cA
    cR
    @9
    cin
    wss
    #
    @40
    wa
    #
    @60
    @18
    @10
    @22
    @11
    @62
    @18
    @10
    wa
    #
    @61
    @22
    @11
    wa
    #
    @40
    @63
    cA
    cR
    @9
    @57
    @18
    @36
    @10
    @18
    @36
    @37
    biimpi
    adantr
    ssind
    @64
    @43
    @40
    @64
    @41
    @42
    @21
    @11
    @41
    @20
    @44
    adantll
    @20
    @42
    @21
    @11
    @46
    ad2antrr
    jca
    @48
    sylib
    anim12i
    an4s
    cA
    cB
    cR
    @9
    mdslmd.1
    mdslmd.2
    mdslmd1lem.5
    @38
    mdslj1i
    sylan2
    anassrs
    @29
    @58
    @6
    @0
    chj
    @58
    @6
    wceq
    @29
    cC
    cD
    cB
    inindir
    a1i
    oveq2d
    eqtr2d
    sseq12d
    bitr4d
    exbiri
    a2d
    syl5
end
