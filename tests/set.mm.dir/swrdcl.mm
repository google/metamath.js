include "cword.mm"
include "wcel.mm"
include "cop.mm"
include "csubstr.mm"
include "co.mm"
include "c0.mm"
include "eleq1.mm"
include "wne.mm"
include "cz.mm"
include "wa.mm"
include "cv.mm"
include "wex.mm"
include "n0.mm"
include "cxp.mm"
include "cvv.mm"
include "c1st.mm"
include "cfv.mm"
include "c2nd.mm"
include "cfzo.mm"
include "cdm.mm"
include "wss.mm"
include "cc0.mm"
include "cmin.mm"
include "caddc.mm"
include "cmpt.mm"
include "cif.mm"
include "df-substr.mm"
include "elmpt2cl2.mm"
include "opelxp.mm"
include "sylib.mm"
include "exlimiv.mm"
include "sylbi.mm"
include "w3a.mm"
include "swrdval.mm"
include "wf.mm"
include "chash.mm"
include "wrdf.mm"
include "3ad2ant1.mm"
include "ad2antrr.mm"
include "simplr.mm"
include "simpr.mm"
include "simpll3.mm"
include "simpll2.mm"
include "fzoaddel2.mm"
include "syl3anc.mm"
include "sseldd.mm"
include "wceq.mm"
include "fdm.mm"
include "syl.mm"
include "eleqtrd.mm"
include "ffvelrnd.mm"
include "eqid.mm"
include "fmptd.mm"
include "iswrdi.mm"
include "wn.mm"
include "wrd0.mm"
include "a1i.mm"
include "ifclda.mm"
include "eqeltrd.mm"
include "3expb.mm"
include "sylan2.mm"
include "pm2.61ne.mm"

theorem swrdcl
  let cA: class A
  let cS: class S
  let cF: class F
  let cL: class L
  let vb: setvar b
  let vs: setvar s
  let vx: setvar x
  let cV: class V
  let cX: class X


  assert |- ( S e. Word A -> ( S substr <. F , L >. ) e. Word A )

  proof
    cS
    cA
    cword
    #
    wcel
    #
    cS
    cF
    cL
    cop
    #
    csubstr
    co
    #
    @0
    wcel
    #
    c0
    @0
    wcel
    #
    @3
    c0
    @3
    c0
    @0
    eleq1
    @3
    c0
    wne
    #
    @1
    cF
    cz
    wcel
    #
    cL
    cz
    wcel
    #
    wa
    #
    @4
    @6
    vx
    cv
    #
    @3
    wcel
    #
    vx
    wex
    @9
    vx
    @3
    n0
    @11
    @9
    vx
    @11
    @2
    cz
    cz
    cxp
    #
    wcel
    @9
    vs
    vb
    cvv
    @12
    vb
    cv
    #
    c1st
    cfv
    #
    @13
    c2nd
    cfv
    #
    cfzo
    co
    vs
    cv
    #
    cdm
    wss
    vx
    cc0
    @15
    @14
    cmin
    co
    cfzo
    co
    @10
    @14
    caddc
    co
    @16
    cfv
    cmpt
    c0
    cif
    cS
    @2
    csubstr
    @10
    vx
    vs
    vb
    df-substr
    elmpt2cl2
    cF
    cL
    cz
    cz
    opelxp
    sylib
    exlimiv
    sylbi
    @1
    @7
    @8
    @4
    @1
    @7
    @8
    w3a
    #
    @3
    cF
    cL
    cfzo
    co
    #
    cS
    cdm
    #
    wss
    #
    vx
    cc0
    cL
    cF
    cmin
    co
    #
    cfzo
    co
    #
    @10
    cF
    caddc
    co
    #
    cS
    cfv
    #
    cmpt
    #
    c0
    cif
    @0
    vx
    cS
    cF
    cL
    @0
    swrdval
    @17
    @20
    @25
    c0
    @0
    @17
    @20
    wa
    #
    @22
    cA
    @25
    wf
    @25
    @0
    wcel
    @26
    vx
    @22
    @24
    cA
    @25
    @26
    @10
    @22
    wcel
    #
    wa
    #
    cc0
    cS
    chash
    cfv
    cfzo
    co
    #
    cA
    @23
    cS
    @17
    @29
    cA
    cS
    wf
    #
    @20
    @27
    @1
    @7
    @30
    @8
    cA
    cS
    wrdf
    3ad2ant1
    ad2antrr
    #
    @28
    @23
    @19
    @29
    @28
    @18
    @19
    @23
    @17
    @20
    @27
    simplr
    @28
    @27
    @8
    @7
    @23
    @18
    wcel
    @26
    @27
    simpr
    @1
    @7
    @8
    @20
    @27
    simpll3
    @1
    @7
    @8
    @20
    @27
    simpll2
    @10
    cL
    cF
    fzoaddel2
    syl3anc
    sseldd
    @28
    @30
    @19
    @29
    wceq
    @31
    @29
    cA
    cS
    fdm
    syl
    eleqtrd
    ffvelrnd
    @25
    eqid
    fmptd
    cA
    @21
    @25
    iswrdi
    syl
    @5
    @17
    @20
    wn
    wa
    cA
    wrd0
    #
    a1i
    ifclda
    eqeltrd
    3expb
    sylan2
    @5
    @1
    @32
    a1i
    pm2.61ne
end
