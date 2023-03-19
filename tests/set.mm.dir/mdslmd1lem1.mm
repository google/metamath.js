include "cmd.mm"
include "wbr.mm"
include "cdmd.mm"
include "wa.mm"
include "wss.mm"
include "chj.mm"
include "co.mm"
include "cin.mm"
include "wi.mm"
include "chincli.mm"
include "chlej1i.mm"
include "wceq.mm"
include "simpr.mm"
include "cch.mm"
include "wcel.mm"
include "w3a.mm"
include "3pm3.2i.mm"
include "dmdsl3.mm"
include "mpan.mm"
include "syl3an.mm"
include "3expb.mm"
include "sseq2d.mm"
include "syl5ib.mm"
include "adantld.mm"
include "imim1d.mm"
include "simpll.mm"
include "ad2antlr.mm"
include "chub2i.mm"
include "jctil.mm"
include "ssin.mm"
include "sylib.mm"
include "inss1.mm"
include "sstr.mm"
include "mpan2.mm"
include "sylan.mm"
include "ancoms.mm"
include "adantll.mm"
include "ad2ant2l.mm"
include "chub1i.mm"
include "jctir.mm"
include "chjcli.mm"
include "chlubi.mm"
include "simprrl.mm"
include "adantr.mm"
include "jca.mm"
include "mdslj1i.mm"
include "syl12anc.mm"
include "simplll.mm"
include "simplrl.mm"
include "ssrin.mm"
include "syl.mm"
include "inindir.mm"
include "syl6sseq.mm"
include "simprl.mm"
include "sstrd.mm"
include "inss2.mm"
include "ad2antll.mm"
include "mdsl3.mm"
include "syl3anc.mm"
include "oveq1d.mm"
include "eqtr2d.mm"
include "ineq1d.mm"
include "syl6eqr.mm"
include "ssinss1.mm"
include "ad2antrl.mm"
include "a1i.mm"
include "oveq12d.mm"
include "sseq12d.mm"
include "wb.mm"
include "simpllr.mm"
include "simplr.mm"
include "sstri.mm"
include "mdslle1i.mm"
include "bitr4d.mm"
include "exbiri.mm"
include "a2d.mm"
include "syld.mm"

theorem mdslmd1lem1
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


  assert |- ( ( ( A MH B /\ B MH* A ) /\ ( ( A C_ C /\ A C_ D ) /\ ( C C_ ( A vH B ) /\ D C_ ( A vH B ) ) ) ) -> ( ( ( R vH A ) C_ D -> ( ( ( R vH A ) vH C ) i^i D ) C_ ( ( R vH A ) vH ( C i^i D ) ) ) -> ( ( ( ( C i^i B ) i^i ( D i^i B ) ) C_ R /\ R C_ ( D i^i B ) ) -> ( ( R vH ( C i^i B ) ) i^i ( D i^i B ) ) C_ ( R vH ( ( C i^i B ) i^i ( D i^i B ) ) ) ) ) )

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
    @6
    wss
    #
    wa
    #
    wa
    #
    wa
    #
    cR
    cA
    chj
    co
    #
    cD
    wss
    #
    @12
    cC
    chj
    co
    #
    cD
    cin
    #
    @12
    cC
    cD
    cin
    #
    chj
    co
    #
    wss
    #
    wi
    cC
    cB
    cin
    #
    cD
    cB
    cin
    #
    cin
    #
    cR
    wss
    #
    cR
    @20
    wss
    #
    wa
    #
    @18
    wi
    @24
    cR
    @19
    chj
    co
    #
    @20
    cin
    #
    cR
    @21
    chj
    co
    #
    wss
    #
    wi
    @11
    @24
    @13
    @18
    @11
    @23
    @13
    @22
    @23
    @12
    @20
    cA
    chj
    co
    #
    wss
    @11
    @13
    cR
    @20
    cA
    mdslmd1lem.5
    cD
    cB
    mdslmd.4
    mdslmd.2
    chincli
    mdslmd.1
    chlej1i
    @11
    @29
    cD
    @12
    @2
    @5
    @9
    @29
    cD
    wceq
    #
    @2
    @1
    @5
    @4
    @9
    @8
    @30
    @0
    @1
    simpr
    @3
    @4
    simpr
    @7
    @8
    simpr
    cA
    cch
    wcel
    #
    cB
    cch
    wcel
    #
    cD
    cch
    wcel
    #
    w3a
    @1
    @4
    @8
    w3a
    @30
    @31
    @32
    @33
    mdslmd.1
    mdslmd.2
    mdslmd.4
    3pm3.2i
    cA
    cB
    cD
    dmdsl3
    mpan
    syl3an
    3expb
    sseq2d
    syl5ib
    adantld
    imim1d
    @11
    @24
    @18
    @28
    @11
    @24
    @28
    @18
    @11
    @24
    wa
    #
    @28
    @15
    cB
    cin
    #
    @17
    cB
    cin
    #
    wss
    #
    @18
    @34
    @26
    @35
    @27
    @36
    @34
    @26
    @14
    cB
    cin
    #
    @20
    cin
    @35
    @34
    @25
    @38
    @20
    @34
    @38
    @12
    cB
    cin
    #
    @19
    chj
    co
    #
    @25
    @34
    @2
    cA
    @12
    cC
    cin
    wss
    #
    @14
    @6
    wss
    #
    @38
    @40
    wceq
    @2
    @10
    @24
    simpll
    #
    @34
    cA
    @12
    wss
    #
    @3
    wa
    @41
    @34
    @3
    @44
    @10
    @3
    @2
    @24
    @3
    @4
    @9
    simpll
    ad2antlr
    cA
    cR
    mdslmd.1
    mdslmd1lem.5
    chub2i
    #
    jctil
    cA
    @12
    cC
    ssin
    sylib
    @34
    @12
    @6
    wss
    #
    @7
    wa
    @42
    @34
    @46
    @7
    @34
    cR
    @6
    wss
    #
    cA
    @6
    wss
    #
    wa
    @46
    @34
    @47
    @48
    @10
    @23
    @47
    @2
    @22
    @9
    @23
    @47
    @5
    @8
    @23
    @47
    @7
    @23
    @8
    @47
    @23
    cR
    cD
    wss
    #
    @8
    @47
    @23
    @20
    cD
    wss
    @49
    cD
    cB
    inss1
    cR
    @20
    cD
    sstr
    mpan2
    cR
    cD
    @6
    sstr
    sylan
    ancoms
    adantll
    adantll
    ad2ant2l
    cA
    cB
    mdslmd.1
    mdslmd.2
    chub1i
    jctir
    cR
    cA
    @6
    mdslmd1lem.5
    mdslmd.1
    cA
    cB
    mdslmd.1
    mdslmd.2
    chjcli
    #
    chlubi
    sylib
    #
    @11
    @7
    @24
    @2
    @5
    @7
    @8
    simprrl
    adantr
    jca
    @12
    cC
    @6
    cR
    cA
    mdslmd1lem.5
    mdslmd.1
    chjcli
    #
    mdslmd.3
    @50
    chlubi
    sylib
    cA
    cB
    @12
    cC
    mdslmd.1
    mdslmd.2
    @52
    mdslmd.3
    mdslj1i
    syl12anc
    @34
    @39
    cR
    @19
    chj
    @34
    @0
    cA
    cB
    cin
    #
    cR
    wss
    #
    cR
    cB
    wss
    #
    @39
    cR
    wceq
    #
    @0
    @1
    @10
    @24
    simplll
    @34
    @53
    @21
    cR
    @34
    @53
    @16
    cB
    cin
    #
    @21
    @34
    cA
    @16
    wss
    #
    @53
    @57
    wss
    @34
    @5
    @58
    @2
    @5
    @9
    @24
    simplrl
    cA
    cC
    cD
    ssin
    sylib
    #
    cA
    @16
    cB
    ssrin
    syl
    cC
    cD
    cB
    inindir
    #
    syl6sseq
    @11
    @22
    @23
    simprl
    sstrd
    @23
    @55
    @11
    @22
    @23
    @20
    cB
    wss
    @55
    cD
    cB
    inss2
    cR
    @20
    cB
    sstr
    mpan2
    ad2antll
    @31
    @32
    cR
    cch
    wcel
    #
    w3a
    @0
    @54
    @55
    w3a
    @56
    @31
    @32
    @61
    mdslmd.1
    mdslmd.2
    mdslmd1lem.5
    3pm3.2i
    cA
    cB
    cR
    mdsl3
    mpan
    syl3anc
    #
    oveq1d
    eqtr2d
    ineq1d
    @14
    cD
    cB
    inindir
    syl6eqr
    @34
    @36
    @39
    @57
    chj
    co
    #
    @27
    @34
    @2
    cA
    @12
    @16
    cin
    wss
    #
    @17
    @6
    wss
    #
    @36
    @63
    wceq
    @43
    @34
    @44
    @58
    wa
    @64
    @34
    @58
    @44
    @59
    @45
    jctil
    cA
    @12
    @16
    ssin
    sylib
    @34
    @46
    @16
    @6
    wss
    #
    wa
    @65
    @34
    @46
    @66
    @51
    @10
    @66
    @2
    @24
    @7
    @66
    @5
    @8
    cC
    cD
    @6
    ssinss1
    ad2antrl
    ad2antlr
    jca
    @12
    @16
    @6
    @52
    cC
    cD
    mdslmd.3
    mdslmd.4
    chincli
    #
    @50
    chlubi
    sylib
    #
    cA
    cB
    @12
    @16
    mdslmd.1
    mdslmd.2
    @52
    @67
    mdslj1i
    syl12anc
    @34
    @39
    cR
    @57
    @21
    chj
    @62
    @57
    @21
    wceq
    @34
    @60
    a1i
    oveq12d
    eqtr2d
    sseq12d
    @34
    @1
    cA
    @15
    @17
    cin
    wss
    #
    @15
    @17
    chj
    co
    @6
    wss
    #
    @18
    @37
    wb
    @0
    @1
    @10
    @24
    simpllr
    @34
    cA
    @15
    wss
    #
    cA
    @17
    wss
    #
    wa
    @69
    @34
    @71
    @72
    @34
    cA
    @14
    wss
    #
    @4
    wa
    @71
    @34
    @4
    @73
    @10
    @4
    @2
    @24
    @3
    @4
    @9
    simplr
    ad2antlr
    cA
    @12
    @14
    @45
    @12
    cC
    @52
    mdslmd.3
    chub1i
    sstri
    jctil
    cA
    @14
    cD
    ssin
    sylib
    cA
    @12
    @17
    @45
    @12
    @16
    @52
    @67
    chub1i
    sstri
    jctir
    cA
    @15
    @17
    ssin
    sylib
    @34
    @15
    @6
    wss
    #
    @65
    wa
    @70
    @34
    @74
    @65
    @10
    @74
    @2
    @24
    @8
    @74
    @5
    @7
    @15
    cD
    wss
    @8
    @74
    @14
    cD
    inss2
    @15
    cD
    @6
    sstr
    mpan
    ad2antll
    ad2antlr
    @68
    jca
    @15
    @17
    @6
    @14
    cD
    @12
    cC
    @52
    mdslmd.3
    chjcli
    mdslmd.4
    chincli
    #
    @12
    @16
    @52
    @67
    chjcli
    #
    @50
    chlubi
    sylib
    cA
    cB
    @15
    @17
    mdslmd.1
    mdslmd.2
    @75
    @76
    mdslle1i
    syl3anc
    bitr4d
    exbiri
    a2d
    syld
end
