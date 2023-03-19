include "cv.mm"
include "cfv.mm"
include "csdm.mm"
include "wbr.mm"
include "wral.mm"
include "wn.mm"
include "wfo.mm"
include "wex.mm"
include "crn.mm"
include "cdif.mm"
include "c0.mm"
include "wne.mm"
include "wcel.mm"
include "wa.mm"
include "cdom.mm"
include "cvv.mm"
include "wfn.mm"
include "fvex.mm"
include "cmpt.mm"
include "eqid.mm"
include "fnmpti.mm"
include "wceq.mm"
include "mptex.mm"
include "fvmpt2.mm"
include "mpan2.mm"
include "fneq1d.mm"
include "mpbiri.mm"
include "fnrndomg.mm"
include "mpsyl.mm"
include "domsdomtr.mm"
include "sylan.mm"
include "sdomdif.mm"
include "syl.mm"
include "ralimiaa.mm"
include "difss.mm"
include "ssexi.mm"
include "ac6c5.mm"
include "equid.mm"
include "wi.mm"
include "cixp.mm"
include "eldifi.mm"
include "eleq1d.mm"
include "syl5ibr.mm"
include "ralimia.mm"
include "jctil.mm"
include "eqeltri.mm"
include "elixp.mm"
include "sylibr.mm"
include "syl6eleqr.mm"
include "wrex.mm"
include "foelrn.mm"
include "expcom.mm"
include "ciun.mm"
include "eleq2i.mm"
include "eliun.mm"
include "bitri.mm"
include "nfra1.mm"
include "nfv.mm"
include "nfan.mm"
include "w3a.mm"
include "ad2antrl.mm"
include "fveq1.mm"
include "fveq1d.mm"
include "sylan9eq.mm"
include "eqcomd.mm"
include "eqtr3d.mm"
include "fnfvelrn.mm"
include "adantl.mm"
include "eqeltrd.mm"
include "3adant1.mm"
include "simp1.mm"
include "simp3l.mm"
include "rsp.mm"
include "eldifn.mm"
include "syl6.mm"
include "sylc.mm"
include "pm2.21dd.mm"
include "3expia.mm"
include "expd.mm"
include "rexlimd.mm"
include "syl5bi.mm"
include "ex.mm"
include "com23.mm"
include "rexlimdv.mm"
include "syl9r.mm"
include "mpd.mm"
include "mt2i.mm"
include "exlimiv.mm"
include "3syl.mm"
include "nexdv.mm"
include "0dom.mm"
include "mpan.mm"
include "0sdom.mm"
include "sylib.mm"
include "ralimi.mm"
include "neeq1i.mm"
include "rgenw.mm"
include "ixpexg.mm"
include "ax-mp.mm"
include "ac9.mm"
include "3bitr4i.mm"
include "wb.mm"
include "iunex.mm"
include "domtri.mm"
include "mp2an.mm"
include "biimpri.mm"
include "fodomr.mm"
include "syl2an.mm"
include "mtand.mm"
include "notnotrd.mm"

theorem konigthlem
  let cA: class A
  let cD: class D
  let cP: class P
  let cS: class S
  let ve: setvar e
  let vf: setvar f
  let vi: setvar i
  let cE: class E
  let cM: class M
  let cN: class N
  let va: setvar a
  assume konigth.1: |- A e. _V
  assume konigth.2: |- S = U_ i e. A ( M ` i )
  assume konigth.3: |- P = X_ i e. A ( N ` i )
  assume konigth.4: |- D = ( i e. A |-> ( a e. ( M ` i ) |-> ( ( f ` a ) ` i ) ) )
  assume konigth.5: |- E = ( i e. A |-> ( e ` i ) )

  disjoint A a
  disjoint A e
  disjoint A f
  disjoint A i
  disjoint a e
  disjoint a f
  disjoint a i
  disjoint e f
  disjoint e i
  disjoint f i
  disjoint D a
  disjoint D e
  disjoint E a
  disjoint E i
  disjoint M a
  disjoint M f
  disjoint N a
  disjoint N e
  disjoint N f
  disjoint P a
  disjoint P e
  disjoint P f
  disjoint S a
  disjoint S e
  disjoint S f
  assert |- ( A. i e. A ( M ` i ) ~< ( N ` i ) -> S ~< P )

  proof
    vi
    cv
    #
    cM
    cfv
    #
    @0
    cN
    cfv
    #
    csdm
    wbr
    #
    vi
    cA
    wral
    #
    cS
    cP
    csdm
    wbr
    #
    @4
    @5
    wn
    #
    cS
    cP
    vf
    cv
    #
    wfo
    #
    vf
    wex
    #
    @4
    @8
    vf
    @4
    @2
    @0
    cD
    cfv
    #
    crn
    #
    cdif
    #
    c0
    wne
    #
    vi
    cA
    wral
    @0
    ve
    cv
    #
    cfv
    #
    @12
    wcel
    #
    vi
    cA
    wral
    #
    ve
    wex
    @8
    wn
    #
    @3
    @13
    vi
    cA
    @0
    cA
    wcel
    #
    @3
    wa
    @11
    @2
    csdm
    wbr
    #
    @13
    @19
    @11
    @1
    cdom
    wbr
    #
    @3
    @20
    @1
    cvv
    wcel
    @19
    @10
    @1
    wfn
    #
    @21
    @0
    cM
    fvex
    #
    @19
    @22
    va
    @1
    @0
    va
    cv
    #
    @7
    cfv
    #
    cfv
    #
    cmpt
    #
    @1
    wfn
    va
    @1
    @26
    @27
    @0
    @25
    fvex
    #
    @27
    eqid
    #
    fnmpti
    @19
    @1
    @10
    @27
    @19
    @27
    cvv
    wcel
    @10
    @27
    wceq
    va
    @1
    @26
    @23
    mptex
    vi
    cA
    @27
    cvv
    cD
    konigth.4
    fvmpt2
    mpan2
    #
    fneq1d
    mpbiri
    #
    @1
    cvv
    @10
    fnrndomg
    mpsyl
    @11
    @1
    @2
    domsdomtr
    sylan
    @11
    @2
    sdomdif
    syl
    ralimiaa
    vi
    cA
    @12
    ve
    konigth.1
    @12
    @2
    @0
    cN
    fvex
    #
    @2
    @11
    difss
    ssexi
    ac6c5
    @17
    @18
    ve
    @17
    @8
    @7
    @7
    wceq
    #
    vf
    equid
    @17
    cE
    cP
    wcel
    #
    @8
    @33
    wn
    #
    wi
    @17
    cE
    vi
    cA
    @2
    cixp
    #
    cP
    @17
    cE
    cA
    wfn
    #
    @0
    cE
    cfv
    #
    @2
    wcel
    #
    vi
    cA
    wral
    #
    wa
    cE
    @36
    wcel
    @17
    @40
    @37
    @16
    @39
    vi
    cA
    @16
    @39
    @19
    @15
    @2
    wcel
    @15
    @2
    @11
    eldifi
    @19
    @38
    @15
    @2
    @19
    @15
    cvv
    wcel
    @38
    @15
    wceq
    #
    @0
    @14
    fvex
    #
    vi
    cA
    @15
    cvv
    cE
    konigth.5
    fvmpt2
    mpan2
    #
    eleq1d
    syl5ibr
    ralimia
    vi
    cA
    @15
    cE
    @42
    konigth.5
    fnmpti
    jctil
    vi
    cA
    @2
    cE
    cE
    vi
    cA
    @15
    cmpt
    cvv
    konigth.5
    vi
    cA
    @15
    konigth.1
    mptex
    eqeltri
    elixp
    sylibr
    konigth.3
    syl6eleqr
    @34
    @8
    cE
    @25
    wceq
    #
    va
    cS
    wrex
    #
    @17
    @35
    @8
    @34
    @45
    va
    cS
    cP
    cE
    @7
    foelrn
    expcom
    @17
    @44
    @35
    va
    cS
    @17
    @44
    @24
    cS
    wcel
    #
    @35
    @17
    @44
    @46
    @35
    wi
    @46
    @24
    @1
    wcel
    #
    vi
    cA
    wrex
    #
    @17
    @44
    wa
    #
    @35
    @46
    @24
    vi
    cA
    @1
    ciun
    #
    wcel
    @48
    cS
    @50
    @24
    konigth.2
    eleq2i
    vi
    @24
    cA
    @1
    eliun
    bitri
    @49
    @47
    @35
    vi
    cA
    @17
    @44
    vi
    @16
    vi
    cA
    nfra1
    @44
    vi
    nfv
    nfan
    @35
    vi
    nfv
    @49
    @19
    @47
    @35
    @17
    @44
    @19
    @47
    wa
    #
    @35
    @17
    @44
    @51
    w3a
    #
    @15
    @11
    wcel
    #
    @35
    @44
    @51
    @53
    @17
    @44
    @51
    wa
    #
    @15
    @24
    @10
    cfv
    #
    @11
    @54
    @38
    @15
    @55
    @19
    @41
    @44
    @47
    @43
    ad2antrl
    @44
    @51
    @38
    @26
    @55
    @0
    cE
    @25
    fveq1
    @51
    @55
    @26
    @19
    @47
    @55
    @24
    @27
    cfv
    #
    @26
    @19
    @24
    @10
    @27
    @30
    fveq1d
    @47
    @26
    cvv
    wcel
    @56
    @26
    wceq
    @28
    va
    @1
    @26
    cvv
    @27
    @29
    fvmpt2
    mpan2
    sylan9eq
    eqcomd
    sylan9eq
    eqtr3d
    @51
    @55
    @11
    wcel
    #
    @44
    @19
    @22
    @47
    @57
    @31
    @1
    @24
    @10
    fnfvelrn
    sylan
    adantl
    eqeltrd
    3adant1
    @52
    @17
    @19
    @53
    wn
    #
    @17
    @44
    @51
    simp1
    @17
    @44
    @19
    @47
    simp3l
    @17
    @19
    @16
    @58
    @16
    vi
    cA
    rsp
    @15
    @2
    @11
    eldifn
    syl6
    sylc
    pm2.21dd
    3expia
    expd
    rexlimd
    syl5bi
    ex
    com23
    rexlimdv
    syl9r
    mpd
    mt2i
    exlimiv
    3syl
    nexdv
    @4
    c0
    cP
    csdm
    wbr
    #
    cP
    cS
    cdom
    wbr
    #
    @9
    @6
    @4
    @2
    c0
    wne
    #
    vi
    cA
    wral
    #
    @59
    @3
    @61
    vi
    cA
    @3
    c0
    @2
    csdm
    wbr
    #
    @61
    c0
    @1
    cdom
    wbr
    @3
    @63
    @1
    @23
    0dom
    c0
    @1
    @2
    domsdomtr
    mpan
    @2
    @32
    0sdom
    sylib
    ralimi
    cP
    c0
    wne
    @36
    c0
    wne
    @59
    @62
    cP
    @36
    c0
    konigth.3
    neeq1i
    cP
    cP
    @36
    cvv
    konigth.3
    @2
    cvv
    wcel
    #
    vi
    cA
    wral
    @36
    cvv
    wcel
    @64
    vi
    cA
    @32
    rgenw
    vi
    cA
    @2
    cvv
    ixpexg
    ax-mp
    eqeltri
    #
    0sdom
    vi
    cA
    @2
    konigth.1
    @32
    ac9
    3bitr4i
    sylibr
    @60
    @6
    cP
    cvv
    wcel
    cS
    cvv
    wcel
    @60
    @6
    wb
    @65
    cS
    @50
    cvv
    konigth.2
    vi
    cA
    @1
    konigth.1
    @23
    iunex
    eqeltri
    cP
    cS
    cvv
    cvv
    domtri
    mp2an
    biimpri
    cS
    cP
    vf
    fodomr
    syl2an
    mtand
    notnotrd
end
