include "cop.mm"
include "csubstr.mm"
include "cdm.mm"
include "wcel.mm"
include "co.mm"
include "c0.mm"
include "wceq.mm"
include "cvv.mm"
include "cz.mm"
include "cxp.mm"
include "wa.mm"
include "opelxp.mm"
include "w3a.mm"
include "cfzo.mm"
include "wss.mm"
include "cc0.mm"
include "cmin.mm"
include "cv.mm"
include "caddc.mm"
include "cfv.mm"
include "cmpt.mm"
include "cif.mm"
include "swrdval.mm"
include "fzo0.mm"
include "0ss.mm"
include "eqsstri.mm"
include "iftruei.mm"
include "zcn.mm"
include "subidd.mm"
include "oveq2d.mm"
include "3ad2ant2.mm"
include "syl6eq.mm"
include "mpteq1d.mm"
include "mpt0.mm"
include "syl5eq.mm"
include "eqtrd.mm"
include "3expb.mm"
include "sylan2b.mm"
include "sylbi.mm"
include "c1st.mm"
include "c2nd.mm"
include "df-substr.mm"
include "ovex.mm"
include "mptex.mm"
include "0ex.mm"
include "ifex.mm"
include "dmmpt2.mm"
include "eleq2s.mm"
include "wn.mm"
include "df-ov.mm"
include "ndmfv.mm"
include "pm2.61i.mm"

theorem swrd00
  let cS: class S
  let cX: class X
  let vb: setvar b
  let vs: setvar s
  let vx: setvar x
  let cF: class F
  let cL: class L
  let cV: class V
  let cA: class A


  assert |- ( S substr <. X , X >. ) = (/)

  proof
    cS
    cX
    cX
    cop
    #
    cop
    #
    csubstr
    cdm
    #
    wcel
    #
    cS
    @0
    csubstr
    co
    #
    c0
    wceq
    #
    @5
    @1
    cvv
    cz
    cz
    cxp
    #
    cxp
    #
    @2
    @1
    @7
    wcel
    cS
    cvv
    wcel
    #
    @0
    @6
    wcel
    #
    wa
    @5
    cS
    @0
    cvv
    @6
    opelxp
    @9
    @8
    cX
    cz
    wcel
    #
    @10
    wa
    @5
    cX
    cX
    cz
    cz
    opelxp
    @8
    @10
    @10
    @5
    @8
    @10
    @10
    w3a
    #
    @4
    cX
    cX
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
    cX
    cX
    cmin
    co
    #
    cfzo
    co
    #
    vx
    cv
    #
    cX
    caddc
    co
    cS
    cfv
    #
    cmpt
    #
    c0
    cif
    #
    c0
    vx
    cS
    cX
    cX
    cvv
    swrdval
    @11
    @20
    @19
    c0
    @14
    @19
    c0
    @12
    c0
    @13
    cX
    fzo0
    @13
    0ss
    eqsstri
    iftruei
    @11
    @19
    vx
    c0
    @18
    cmpt
    c0
    @11
    vx
    @16
    c0
    @18
    @11
    @16
    cc0
    cc0
    cfzo
    co
    #
    c0
    @10
    @8
    @16
    @21
    wceq
    @10
    @10
    @15
    cc0
    cc0
    cfzo
    @10
    cX
    cX
    zcn
    subidd
    oveq2d
    3ad2ant2
    cc0
    fzo0
    syl6eq
    mpteq1d
    vx
    @18
    mpt0
    syl6eq
    syl5eq
    eqtrd
    3expb
    sylan2b
    sylbi
    vs
    vb
    cvv
    @6
    vb
    cv
    #
    c1st
    cfv
    #
    @22
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
    #
    vx
    cc0
    @24
    @23
    cmin
    co
    #
    cfzo
    co
    #
    @17
    @23
    caddc
    co
    @25
    cfv
    #
    cmpt
    #
    c0
    cif
    csubstr
    vx
    vs
    vb
    df-substr
    @26
    @30
    c0
    vx
    @28
    @29
    cc0
    @27
    cfzo
    ovex
    mptex
    0ex
    ifex
    dmmpt2
    eleq2s
    @3
    wn
    @4
    @1
    csubstr
    cfv
    c0
    cS
    @0
    csubstr
    df-ov
    @1
    csubstr
    ndmfv
    syl5eq
    pm2.61i
end
