include "cdm.mm"
include "wss.mm"
include "cv.mm"
include "csuc.mm"
include "cres.mm"
include "cslt.mm"
include "wbr.mm"
include "wn.mm"
include "wral.mm"
include "w3a.mm"
include "csur.mm"
include "wcel.mm"
include "wa.mm"
include "cun.mm"
include "wi.mm"
include "unss.mm"
include "ssralv.mm"
include "sylbi.mm"
include "3impia.mm"
include "wceq.mm"
include "breq1.mm"
include "notbid.mm"
include "biimpd.mm"
include "wor.mm"
include "sltso.mm"
include "sonr.mm"
include "mpan.mm"
include "adantr.mm"
include "impel.mm"
include "adantrr.mm"
include "ex.mm"
include "wne.mm"
include "simprl.mm"
include "cfv.mm"
include "con0.mm"
include "crab.mm"
include "cint.mm"
include "simprll.mm"
include "simprlr.mm"
include "simpl.mm"
include "nosepne.mm"
include "syl3anc.mm"
include "nosepon.mm"
include "sucidg.mm"
include "syl.mm"
include "fvresd.mm"
include "3netr4d.mm"
include "neneqd.mm"
include "fveq1.mm"
include "nsyl.mm"
include "nosepdm.mm"
include "simprr.mm"
include "suceq.mm"
include "reseq2d.mm"
include "breq12d.mm"
include "rspcv.mm"
include "sylc.mm"
include "w3o.mm"
include "suceloni.mm"
include "noreson.mm"
include "syl2anc.mm"
include "solin.mm"
include "ecase23d.mm"
include "sltres.mm"
include "mpd.mm"
include "soasym.mm"
include "pm2.61ine.mm"
include "sylan2.mm"

theorem noresle
  let cA: class A
  let cS: class S
  let cU: class U
  let vg: setvar g
  let vx: setvar x

  disjoint S g
  disjoint U g
  disjoint A g
  disjoint S x
  disjoint g x
  disjoint U x
  disjoint A x
  assert |- ( ( ( U e. No /\ S e. No ) /\ ( dom U C_ A /\ dom S C_ A /\ A. g e. A -. ( S |` suc g ) <s ( U |` suc g ) ) ) -> -. S <s U )

  proof
    cU
    cdm
    #
    cA
    wss
    #
    cS
    cdm
    #
    cA
    wss
    #
    cS
    vg
    cv
    #
    csuc
    #
    cres
    #
    cU
    @5
    cres
    #
    cslt
    wbr
    #
    wn
    #
    vg
    cA
    wral
    #
    w3a
    cU
    csur
    wcel
    #
    cS
    csur
    wcel
    #
    wa
    #
    @9
    vg
    @0
    @2
    cun
    #
    wral
    #
    cS
    cU
    cslt
    wbr
    #
    wn
    #
    @1
    @3
    @10
    @15
    @1
    @3
    wa
    @14
    cA
    wss
    @10
    @15
    wi
    @0
    @2
    cA
    unss
    @9
    vg
    @14
    cA
    ssralv
    sylbi
    3impia
    @13
    @15
    wa
    #
    @17
    wi
    cU
    cS
    cU
    cS
    wceq
    #
    @18
    @17
    @19
    @13
    @17
    @15
    @19
    cU
    cU
    cslt
    wbr
    #
    wn
    #
    @17
    @13
    @19
    @21
    @17
    @19
    @20
    @16
    cU
    cS
    cU
    cslt
    breq1
    notbid
    biimpd
    @11
    @21
    @12
    csur
    cslt
    wor
    #
    @11
    @21
    sltso
    csur
    cU
    cslt
    sonr
    mpan
    adantr
    impel
    adantrr
    ex
    cU
    cS
    wne
    #
    @18
    @17
    @23
    @18
    wa
    #
    @13
    cU
    cS
    cslt
    wbr
    #
    @17
    @23
    @13
    @15
    simprl
    @24
    cU
    vx
    cv
    #
    cU
    cfv
    @26
    cS
    cfv
    wne
    vx
    con0
    crab
    cint
    #
    csuc
    #
    cres
    #
    cS
    @28
    cres
    #
    cslt
    wbr
    #
    @25
    @24
    @31
    @29
    @30
    wceq
    #
    @30
    @29
    cslt
    wbr
    #
    @24
    @27
    @29
    cfv
    #
    @27
    @30
    cfv
    #
    wceq
    @32
    @24
    @34
    @35
    @24
    @27
    cU
    cfv
    #
    @27
    cS
    cfv
    #
    @34
    @35
    @24
    @11
    @12
    @23
    @36
    @37
    wne
    @23
    @11
    @12
    @15
    simprll
    #
    @23
    @11
    @12
    @15
    simprlr
    #
    @23
    @18
    simpl
    #
    vx
    cU
    cS
    nosepne
    syl3anc
    @24
    @27
    @28
    cU
    @24
    @27
    con0
    wcel
    #
    @27
    @28
    wcel
    @24
    @11
    @12
    @23
    @41
    @38
    @39
    @40
    vx
    cU
    cS
    nosepon
    syl3anc
    #
    @27
    con0
    sucidg
    syl
    #
    fvresd
    @24
    @27
    @28
    cS
    @43
    fvresd
    3netr4d
    neneqd
    @27
    @29
    @30
    fveq1
    nsyl
    @24
    @27
    @14
    wcel
    #
    @15
    @33
    wn
    #
    @24
    @11
    @12
    @23
    @44
    @38
    @39
    @40
    vx
    cU
    cS
    nosepdm
    syl3anc
    @23
    @13
    @15
    simprr
    @9
    @45
    vg
    @27
    @14
    @4
    @27
    wceq
    #
    @8
    @33
    @46
    @6
    @30
    @7
    @29
    cslt
    @46
    @5
    @28
    cS
    @4
    @27
    suceq
    #
    reseq2d
    @46
    @5
    @28
    cU
    @47
    reseq2d
    breq12d
    notbid
    rspcv
    sylc
    @24
    @29
    csur
    wcel
    #
    @30
    csur
    wcel
    #
    @31
    @32
    @33
    w3o
    #
    @24
    @11
    @28
    con0
    wcel
    #
    @48
    @38
    @24
    @41
    @51
    @42
    @27
    suceloni
    syl
    #
    cU
    @28
    noreson
    syl2anc
    @24
    @12
    @51
    @49
    @39
    @52
    cS
    @28
    noreson
    syl2anc
    @22
    @48
    @49
    wa
    @50
    sltso
    csur
    @29
    @30
    cslt
    solin
    mpan
    syl2anc
    ecase23d
    @24
    @11
    @12
    @51
    @31
    @25
    wi
    @38
    @39
    @52
    cU
    cS
    @28
    sltres
    syl3anc
    mpd
    @22
    @13
    @25
    @17
    wi
    sltso
    csur
    cslt
    cU
    cS
    soasym
    mpan
    sylc
    ex
    pm2.61ine
    sylan2
end
