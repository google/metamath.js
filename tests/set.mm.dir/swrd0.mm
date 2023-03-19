include "c0.mm"
include "cop.mm"
include "csubstr.mm"
include "cdm.mm"
include "wcel.mm"
include "co.mm"
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
include "clt.mm"
include "wbr.mm"
include "wn.mm"
include "fzonlt0.mm"
include "biimprd.mm"
include "con2d.mm"
include "impcom.mm"
include "ss0.mm"
include "nsyl.mm"
include "dm0.mm"
include "a1i.mm"
include "sseq2d.mm"
include "mtbird.mm"
include "iffalsed.mm"
include "0ss.mm"
include "biimpac.mm"
include "3sstr4d.mm"
include "iftrued.mm"
include "cle.mm"
include "cr.mm"
include "wb.mm"
include "zre.mm"
include "lenlt.mm"
include "bicomd.mm"
include "syl2anr.mm"
include "fzo0n.mm"
include "bitrd.mm"
include "mpteq1d.mm"
include "dmeqd.mm"
include "wral.mm"
include "ral0.mm"
include "dmmptg.mm"
include "mp1i.mm"
include "eqtrd.mm"
include "wrel.mm"
include "mptrel.mm"
include "reldm0.mm"
include "mpbird.mm"
include "pm2.61ian.mm"
include "3adant1.mm"
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
include "df-ov.mm"
include "ndmfv.mm"
include "syl5eq.mm"
include "pm2.61i.mm"

theorem swrd0
  let cF: class F
  let cL: class L
  let vx: setvar x
  let vb: setvar b
  let vs: setvar s
  let vz: setvar z


  assert |- ( (/) substr <. F , L >. ) = (/)

  proof
    c0
    cF
    cL
    cop
    #
    cop
    #
    csubstr
    cdm
    #
    wcel
    #
    c0
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
    c0
    cvv
    wcel
    #
    @0
    @6
    wcel
    #
    wa
    @5
    c0
    @0
    cvv
    @6
    opelxp
    @9
    @8
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
    @5
    cF
    cL
    cz
    cz
    opelxp
    @8
    @10
    @11
    @5
    @8
    @10
    @11
    w3a
    @4
    cF
    cL
    cfzo
    co
    #
    c0
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
    cfzo
    co
    #
    vx
    cv
    cF
    caddc
    co
    c0
    cfv
    #
    cmpt
    #
    c0
    cif
    #
    c0
    vx
    c0
    cF
    cL
    cvv
    swrdval
    @10
    @11
    @19
    c0
    wceq
    #
    @8
    cF
    cL
    clt
    wbr
    #
    @12
    @20
    @21
    @12
    wa
    #
    @15
    @18
    c0
    @22
    @15
    @13
    c0
    wss
    #
    @22
    @13
    c0
    wceq
    #
    @23
    @12
    @21
    @24
    wn
    @12
    @24
    @21
    @12
    @21
    wn
    #
    @24
    cF
    cL
    fzonlt0
    #
    biimprd
    con2d
    impcom
    @13
    ss0
    nsyl
    @22
    @14
    c0
    @13
    @14
    c0
    wceq
    #
    @22
    dm0
    a1i
    sseq2d
    mtbird
    iffalsed
    @25
    @12
    wa
    #
    @19
    @18
    c0
    @28
    @15
    @18
    c0
    @28
    c0
    c0
    @13
    @14
    c0
    c0
    wss
    @28
    c0
    0ss
    a1i
    @12
    @25
    @24
    @26
    biimpac
    @27
    @28
    dm0
    a1i
    3sstr4d
    iftrued
    @28
    @18
    c0
    wceq
    #
    @18
    cdm
    #
    c0
    wceq
    #
    @28
    @30
    vx
    c0
    @17
    cmpt
    #
    cdm
    #
    c0
    @28
    @18
    @32
    @28
    vx
    @16
    c0
    @17
    @12
    @25
    @16
    c0
    wceq
    #
    @12
    @25
    cL
    cF
    cle
    wbr
    #
    @34
    @11
    cL
    cr
    wcel
    #
    cF
    cr
    wcel
    #
    @25
    @35
    wb
    @10
    cL
    zre
    cF
    zre
    @36
    @37
    wa
    @35
    @25
    cL
    cF
    lenlt
    bicomd
    syl2anr
    cF
    cL
    fzo0n
    bitrd
    biimpac
    mpteq1d
    dmeqd
    @17
    cvv
    wcel
    #
    vx
    c0
    wral
    @33
    c0
    wceq
    @28
    @38
    vx
    ral0
    vx
    c0
    @17
    cvv
    dmmptg
    mp1i
    eqtrd
    @18
    wrel
    @29
    @31
    wb
    @28
    vx
    @16
    @17
    mptrel
    @18
    reldm0
    mp1i
    mpbird
    eqtrd
    pm2.61ian
    3adant1
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
    @39
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
    vz
    cc0
    @41
    @40
    cmin
    co
    #
    cfzo
    co
    #
    vz
    cv
    @40
    caddc
    co
    @42
    cfv
    #
    cmpt
    #
    c0
    cif
    csubstr
    vz
    vs
    vb
    df-substr
    @43
    @47
    c0
    vz
    @45
    @46
    cc0
    @44
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
    c0
    @0
    csubstr
    df-ov
    @1
    csubstr
    ndmfv
    syl5eq
    pm2.61i
end
