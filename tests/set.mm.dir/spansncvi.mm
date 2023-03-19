include "wpss.mm"
include "csn.mm"
include "cspn.mm"
include "cfv.mm"
include "chj.mm"
include "co.mm"
include "wss.mm"
include "wa.mm"
include "simpr.mm"
include "pssss.mm"
include "adantr.mm"
include "wi.mm"
include "cv.mm"
include "wcel.mm"
include "wn.mm"
include "wex.mm"
include "pssnel.mm"
include "ssel2.mm"
include "cva.mm"
include "wceq.mm"
include "wrex.mm"
include "cph.mm"
include "spansnji.mm"
include "eleq2i.mm"
include "spansnchi.mm"
include "chseli.mm"
include "bitr3i.mm"
include "cmv.mm"
include "eleq1.mm"
include "biimpac.mm"
include "sselda.mm"
include "csh.mm"
include "chshii.mm"
include "shsubcl.mm"
include "mp3an1.mm"
include "syl2an.mm"
include "exp43.mm"
include "com14.mm"
include "imp45.mm"
include "chil.mm"
include "cheli.mm"
include "hvpncan2.mm"
include "eleq1d.mm"
include "syl5ib.mm"
include "imp.mm"
include "anandis.mm"
include "exp45.mm"
include "imp41.mm"
include "adantrr.mm"
include "c0v.mm"
include "wne.mm"
include "oveq2.mm"
include "ax-hvaddid.mm"
include "syl.mm"
include "sylan9eqr.mm"
include "eqeq2d.mm"
include "eleq1a.mm"
include "sylbid.mm"
include "impancom.mm"
include "necon3bd.mm"
include "spansnss.mm"
include "mpan.mm"
include "spansneleq.mm"
include "sseq1d.mm"
include "ancoms.mm"
include "sylan2.mm"
include "exp44.mm"
include "com12.mm"
include "adantrl.mm"
include "mpd.mm"
include "rexlimivv.mm"
include "sylbi.mm"
include "anandirs.mm"
include "expimpd.mm"
include "exlimdv.mm"
include "syl5.mm"
include "ex.mm"
include "pm2.43d.mm"
include "impcom.mm"
include "chlubii.mm"
include "syl2anc.mm"
include "eqssd.mm"

theorem spansncvi
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume spansncv.1: |- A e. CH
  assume spansncv.2: |- B e. CH
  assume spansncv.3: |- C e. ~H


  assert |- ( ( A C. B /\ B C_ ( A vH ( span ` { C } ) ) ) -> B = ( A vH ( span ` { C } ) ) )

  proof
    cA
    cB
    wpss
    #
    cB
    cA
    cC
    csn
    cspn
    cfv
    #
    chj
    co
    #
    wss
    #
    wa
    #
    cB
    @2
    @0
    @3
    simpr
    @4
    cA
    cB
    wss
    #
    @1
    cB
    wss
    #
    @2
    cB
    wss
    @0
    @5
    @3
    cA
    cB
    pssss
    #
    adantr
    @3
    @0
    @6
    @3
    @0
    @6
    @3
    @0
    @0
    @6
    wi
    @0
    vx
    cv
    #
    cB
    wcel
    #
    @8
    cA
    wcel
    #
    wn
    #
    wa
    #
    vx
    wex
    @3
    @0
    wa
    #
    @6
    vx
    cA
    cB
    pssnel
    @13
    @12
    @6
    vx
    @13
    @9
    @11
    @6
    @3
    @0
    @9
    @11
    @6
    wi
    #
    @3
    @9
    wa
    #
    @0
    @9
    wa
    #
    @14
    @15
    @8
    @2
    wcel
    #
    @16
    @14
    wi
    #
    cB
    @2
    @8
    ssel2
    @17
    @8
    vy
    cv
    #
    vz
    cv
    #
    cva
    co
    #
    wceq
    #
    vz
    @1
    wrex
    vy
    cA
    wrex
    #
    @18
    @17
    @8
    cA
    @1
    cph
    co
    #
    wcel
    @23
    @24
    @2
    @8
    cA
    cC
    spansncv.1
    spansncv.3
    spansnji
    eleq2i
    vy
    vz
    cA
    @1
    @8
    spansncv.1
    cC
    spansncv.3
    spansnchi
    #
    chseli
    bitr3i
    @22
    @18
    vy
    vz
    cA
    @1
    @19
    cA
    wcel
    #
    @20
    @1
    wcel
    #
    wa
    #
    @22
    @16
    @11
    @6
    @28
    @22
    wa
    #
    @16
    @11
    wa
    wa
    @20
    cB
    wcel
    #
    @6
    @29
    @16
    @30
    @11
    @26
    @27
    @22
    @16
    @30
    @26
    @27
    @22
    @16
    @30
    @26
    @27
    @22
    @16
    wa
    #
    @30
    @28
    @26
    @31
    wa
    #
    @30
    @32
    @21
    @19
    cmv
    co
    #
    cB
    wcel
    #
    @28
    @30
    @26
    @22
    @0
    @9
    @34
    @9
    @22
    @0
    @26
    @34
    @9
    @22
    @0
    @26
    @34
    @9
    @22
    wa
    @21
    cB
    wcel
    #
    @19
    cB
    wcel
    #
    @34
    @0
    @26
    wa
    @22
    @9
    @35
    @8
    @21
    cB
    eleq1
    biimpac
    @0
    cA
    cB
    @19
    @7
    sselda
    cB
    csh
    wcel
    #
    @35
    @36
    @34
    cB
    spansncv.2
    chshii
    #
    @21
    @19
    cB
    shsubcl
    mp3an1
    syl2an
    exp43
    com14
    imp45
    @28
    @33
    @20
    cB
    @26
    @19
    chil
    wcel
    #
    @20
    chil
    wcel
    @33
    @20
    wceq
    @27
    @19
    cA
    spansncv.1
    cheli
    #
    @20
    @1
    @25
    cheli
    @19
    @20
    hvpncan2
    syl2an
    eleq1d
    syl5ib
    imp
    anandis
    exp45
    imp41
    adantrr
    @29
    @11
    @30
    @6
    wi
    #
    @16
    @26
    @27
    @22
    @11
    @41
    @27
    @26
    @22
    @11
    @41
    wi
    wi
    @27
    @26
    @22
    @11
    @41
    @26
    @22
    wa
    #
    @11
    wa
    @27
    @20
    c0v
    wne
    #
    @41
    @42
    @11
    @43
    @42
    @10
    @20
    c0v
    @26
    @20
    c0v
    wceq
    #
    @22
    @10
    @26
    @44
    wa
    #
    @22
    @8
    @19
    wceq
    #
    @10
    @45
    @21
    @19
    @8
    @44
    @26
    @21
    @19
    c0v
    cva
    co
    #
    @19
    @20
    c0v
    @19
    cva
    oveq2
    @26
    @39
    @47
    @19
    wceq
    @40
    @19
    ax-hvaddid
    syl
    sylan9eqr
    eqeq2d
    @26
    @46
    @10
    wi
    @44
    @19
    cA
    @8
    eleq1a
    adantr
    sylbid
    impancom
    necon3bd
    imp
    @43
    @27
    @41
    @30
    @20
    csn
    cspn
    cfv
    #
    cB
    wss
    #
    @43
    @27
    wa
    #
    @6
    @37
    @30
    @49
    @38
    cB
    @20
    spansnss
    mpan
    @50
    @48
    @1
    cB
    @43
    @27
    @48
    @1
    wceq
    #
    cC
    chil
    wcel
    @43
    @27
    @51
    wi
    spansncv.3
    @20
    cC
    spansneleq
    mpan
    imp
    sseq1d
    syl5ib
    ancoms
    sylan2
    exp44
    com12
    imp41
    adantrl
    mpd
    exp43
    rexlimivv
    sylbi
    syl
    imp
    anandirs
    expimpd
    exlimdv
    syl5
    ex
    pm2.43d
    impcom
    cA
    @1
    cB
    spansncv.1
    @25
    spansncv.2
    chlubii
    syl2anc
    eqssd
end
