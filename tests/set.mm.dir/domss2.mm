include "wf1.mm"
include "wcel.mm"
include "w3a.mm"
include "crn.mm"
include "wf1o.mm"
include "wss.mm"
include "ccom.mm"
include "cid.mm"
include "cres.mm"
include "wceq.mm"
include "cdif.mm"
include "cuni.mm"
include "cpw.mm"
include "csn.mm"
include "cxp.mm"
include "cun.mm"
include "c1st.mm"
include "ccnv.mm"
include "cin.mm"
include "c0.mm"
include "f1f1orn.mm"
include "3ad2ant1.mm"
include "cvv.mm"
include "simp2.mm"
include "rnexg.mm"
include "syl.mm"
include "uniexg.mm"
include "pwexg.mm"
include "3syl.mm"
include "1stconst.mm"
include "cen.mm"
include "wbr.mm"
include "wa.mm"
include "difexg.mm"
include "3ad2ant3.mm"
include "disjen.mm"
include "syl2anc.mm"
include "simpld.mm"
include "disjdif.mm"
include "a1i.mm"
include "f1oun.mm"
include "syl22anc.mm"
include "wb.mm"
include "undif2.mm"
include "wf.mm"
include "f1f.mm"
include "frn.mm"
include "ssequn1.mm"
include "sylib.mm"
include "syl5eq.mm"
include "f1oeq3.mm"
include "mpbid.mm"
include "f1ocnv.mm"
include "f1oeq1.mm"
include "ax-mp.mm"
include "sylibr.mm"
include "wfo.mm"
include "f1ofo.mm"
include "forn.mm"
include "mpbird.mm"
include "ssun1.mm"
include "syl5sseqr.mm"
include "ssid.mm"
include "cores.mm"
include "cdm.mm"
include "dmres.mm"
include "f1odm.mm"
include "ineq2d.mm"
include "syl6eq.mm"
include "wrel.mm"
include "relres.mm"
include "reldm0.mm"
include "uneq2d.mm"
include "cnvun.mm"
include "eqtri.mm"
include "reseq1i.mm"
include "resundir.mm"
include "df-rn.mm"
include "reseq2i.mm"
include "relcnv.mm"
include "resdm.mm"
include "uneq1i.mm"
include "3eqtrri.mm"
include "un0.mm"
include "3eqtr3g.mm"
include "coeq1d.mm"
include "f1cocnv1.mm"
include "eqtrd.mm"
include "syl5eqr.mm"
include "3jca.mm"

theorem domss2
  let cA: class A
  let cB: class B
  let cF: class F
  let cG: class G
  let cV: class V
  let cW: class W
  assume domss2.1: |- G = `' ( F u. ( 1st |` ( ( B \ ran F ) X. { ~P U. ran A } ) ) )


  assert |- ( ( F : A -1-1-> B /\ A e. V /\ B e. W ) -> ( G : B -1-1-onto-> ran G /\ A C_ ran G /\ ( G o. F ) = ( _I |` A ) ) )

  proof
    cA
    cB
    cF
    wf1
    #
    cA
    cV
    wcel
    #
    cB
    cW
    wcel
    #
    w3a
    #
    cB
    cG
    crn
    #
    cG
    wf1o
    #
    cA
    @4
    wss
    cG
    cF
    ccom
    #
    cid
    cA
    cres
    #
    wceq
    @3
    @5
    cB
    cA
    cB
    cF
    crn
    #
    cdif
    #
    cA
    crn
    #
    cuni
    #
    cpw
    #
    csn
    cxp
    #
    cun
    #
    cG
    wf1o
    #
    @3
    cB
    @14
    cF
    c1st
    @13
    cres
    #
    cun
    #
    ccnv
    #
    wf1o
    #
    @15
    @3
    @14
    cB
    @17
    wf1o
    #
    @19
    @3
    @14
    @8
    @9
    cun
    #
    @17
    wf1o
    #
    @20
    @3
    cA
    @8
    cF
    wf1o
    #
    @13
    @9
    @16
    wf1o
    #
    cA
    @13
    cin
    c0
    wceq
    #
    @8
    @9
    cin
    #
    c0
    wceq
    #
    @22
    @0
    @1
    @23
    @2
    cA
    cB
    cF
    f1f1orn
    3ad2ant1
    @3
    @12
    cvv
    wcel
    #
    @24
    @3
    @10
    cvv
    wcel
    #
    @11
    cvv
    wcel
    @28
    @3
    @1
    @29
    @0
    @1
    @2
    simp2
    #
    cA
    cV
    rnexg
    syl
    @10
    cvv
    uniexg
    @11
    cvv
    pwexg
    3syl
    @9
    @12
    cvv
    1stconst
    syl
    #
    @3
    @25
    @13
    @9
    cen
    wbr
    #
    @3
    @1
    @9
    cvv
    wcel
    #
    @25
    @32
    wa
    @30
    @2
    @0
    @33
    @1
    cB
    @8
    cW
    difexg
    3ad2ant3
    cA
    @9
    cV
    cvv
    disjen
    syl2anc
    simpld
    @27
    @3
    @8
    cB
    disjdif
    #
    a1i
    cA
    @8
    @13
    @9
    cF
    @16
    f1oun
    syl22anc
    @3
    @21
    cB
    wceq
    @22
    @20
    wb
    @3
    @21
    @8
    cB
    cun
    #
    cB
    @8
    cB
    undif2
    @3
    @8
    cB
    wss
    #
    @35
    cB
    wceq
    @3
    cA
    cB
    cF
    wf
    #
    @36
    @0
    @1
    @37
    @2
    cA
    cB
    cF
    f1f
    3ad2ant1
    cA
    cB
    cF
    frn
    syl
    @8
    cB
    ssequn1
    sylib
    syl5eq
    @21
    cB
    @14
    @17
    f1oeq3
    syl
    mpbid
    @14
    cB
    @17
    f1ocnv
    syl
    cG
    @18
    wceq
    @15
    @19
    wb
    domss2.1
    cB
    @14
    cG
    @18
    f1oeq1
    ax-mp
    sylibr
    #
    @3
    @4
    @14
    wceq
    #
    @5
    @15
    wb
    @3
    @15
    cB
    @14
    cG
    wfo
    @39
    @38
    cB
    @14
    cG
    f1ofo
    cB
    @14
    cG
    forn
    3syl
    #
    @4
    @14
    cB
    cG
    f1oeq3
    syl
    mpbird
    @3
    @14
    cA
    @4
    cA
    @13
    ssun1
    @40
    syl5sseqr
    @3
    @6
    cG
    @8
    cres
    #
    cF
    ccom
    #
    @7
    @8
    @8
    wss
    @42
    @6
    wceq
    @8
    ssid
    cG
    cF
    @8
    cores
    ax-mp
    @3
    @42
    cF
    ccnv
    #
    cF
    ccom
    #
    @7
    @3
    @41
    @43
    cF
    @3
    @43
    @16
    ccnv
    #
    @8
    cres
    #
    cun
    #
    @43
    c0
    cun
    @41
    @43
    @3
    @46
    c0
    @43
    @3
    @46
    cdm
    #
    c0
    wceq
    #
    @46
    c0
    wceq
    #
    @3
    @48
    @8
    @45
    cdm
    #
    cin
    #
    c0
    @45
    @8
    dmres
    @3
    @52
    @26
    c0
    @3
    @51
    @9
    @8
    @3
    @24
    @9
    @13
    @45
    wf1o
    @51
    @9
    wceq
    @31
    @13
    @9
    @16
    f1ocnv
    @9
    @13
    @45
    f1odm
    3syl
    ineq2d
    @34
    syl6eq
    syl5eq
    @46
    wrel
    @50
    @49
    wb
    @45
    @8
    relres
    @46
    reldm0
    ax-mp
    sylibr
    uneq2d
    @41
    @43
    @45
    cun
    #
    @8
    cres
    @43
    @8
    cres
    #
    @46
    cun
    @47
    cG
    @53
    @8
    cG
    @18
    @53
    domss2.1
    cF
    @16
    cnvun
    eqtri
    reseq1i
    @43
    @45
    @8
    resundir
    @54
    @43
    @46
    @54
    @43
    @43
    cdm
    #
    cres
    #
    @43
    @8
    @55
    @43
    cF
    df-rn
    reseq2i
    @43
    wrel
    @56
    @43
    wceq
    cF
    relcnv
    @43
    resdm
    ax-mp
    eqtri
    uneq1i
    3eqtrri
    @43
    un0
    3eqtr3g
    coeq1d
    @0
    @1
    @44
    @7
    wceq
    @2
    cA
    cB
    cF
    f1cocnv1
    3ad2ant1
    eqtrd
    syl5eqr
    3jca
end
