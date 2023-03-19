include "cconn.mm"
include "wcel.mm"
include "wfo.mm"
include "ccn.mm"
include "co.mm"
include "w3a.mm"
include "ctop.mm"
include "ccld.mm"
include "cfv.mm"
include "cin.mm"
include "c0.mm"
include "cpr.mm"
include "wss.mm"
include "cntop2.mm"
include "3ad2ant3.mm"
include "cv.mm"
include "wa.mm"
include "wceq.mm"
include "wo.mm"
include "wn.mm"
include "wne.mm"
include "df-ne.mm"
include "ccnv.mm"
include "cima.mm"
include "cuni.mm"
include "cdm.mm"
include "eqid.mm"
include "simpl1.mm"
include "simpl3.mm"
include "inss1.mm"
include "simprl.mm"
include "sseldi.mm"
include "cnima.mm"
include "syl2anc.mm"
include "crn.mm"
include "elssuni.mm"
include "syl.mm"
include "syl6sseqr.mm"
include "simpl2.mm"
include "forn.mm"
include "sseqtr4d.mm"
include "df-rn.mm"
include "syl6sseq.mm"
include "sseqin2.mm"
include "sylib.mm"
include "simprr.mm"
include "eqnetrd.mm"
include "imadisj.mm"
include "necon3bii.mm"
include "sylibr.mm"
include "inss2.mm"
include "cnclima.mm"
include "connclo.mm"
include "wf.mm"
include "cnf.mm"
include "fdm.mm"
include "3syl.mm"
include "fof.mm"
include "3eqtr2d.mm"
include "imaeq2d.mm"
include "foimacnv.mm"
include "foima.mm"
include "3eqtr3d.mm"
include "expr.mm"
include "syl5bir.mm"
include "orrd.mm"
include "vex.mm"
include "elpr.mm"
include "ex.mm"
include "ssrdv.mm"
include "isconn2.mm"
include "sylanbrc.mm"

theorem cnconn
  let cF: class F
  let cJ: class J
  let cK: class K
  let cX: class X
  let cY: class Y
  let vx: setvar x
  assume cnconn.2: |- Y = U. K


  assert |- ( ( J e. Conn /\ F : X -onto-> Y /\ F e. ( J Cn K ) ) -> K e. Conn )

  proof
    cJ
    cconn
    wcel
    #
    cX
    cY
    cF
    wfo
    #
    cF
    cJ
    cK
    ccn
    co
    wcel
    #
    w3a
    #
    cK
    ctop
    wcel
    #
    cK
    cK
    ccld
    cfv
    #
    cin
    #
    c0
    cY
    cpr
    #
    wss
    cK
    cconn
    wcel
    @2
    @0
    @4
    @1
    cF
    cJ
    cK
    cntop2
    3ad2ant3
    @3
    vx
    @6
    @7
    @3
    vx
    cv
    #
    @6
    wcel
    #
    @8
    @7
    wcel
    #
    @3
    @9
    wa
    #
    @8
    c0
    wceq
    #
    @8
    cY
    wceq
    #
    wo
    @10
    @11
    @12
    @13
    @12
    wn
    @8
    c0
    wne
    #
    @11
    @13
    @8
    c0
    df-ne
    @3
    @9
    @14
    @13
    @3
    @9
    @14
    wa
    #
    wa
    #
    cF
    cF
    ccnv
    #
    @8
    cima
    #
    cima
    #
    cF
    cX
    cima
    #
    @8
    cY
    @16
    @18
    cX
    cF
    @16
    @18
    cJ
    cuni
    #
    cF
    cdm
    #
    cX
    @16
    @18
    cJ
    @21
    @21
    eqid
    #
    @0
    @1
    @2
    @15
    simpl1
    @16
    @2
    @8
    cK
    wcel
    #
    @18
    cJ
    wcel
    @0
    @1
    @2
    @15
    simpl3
    #
    @16
    @6
    cK
    @8
    cK
    @5
    inss1
    @3
    @9
    @14
    simprl
    #
    sseldi
    #
    @8
    cF
    cJ
    cK
    cnima
    syl2anc
    @16
    @17
    cdm
    #
    @8
    cin
    #
    c0
    wne
    @18
    c0
    wne
    @16
    @29
    @8
    c0
    @16
    @8
    @28
    wss
    @29
    @8
    wceq
    @16
    @8
    cF
    crn
    #
    @28
    @16
    @8
    cY
    @30
    @16
    @8
    cK
    cuni
    #
    cY
    @16
    @24
    @8
    @31
    wss
    @27
    @8
    cK
    elssuni
    syl
    cnconn.2
    syl6sseqr
    #
    @16
    @1
    @30
    cY
    wceq
    @0
    @1
    @2
    @15
    simpl2
    #
    cX
    cY
    cF
    forn
    syl
    sseqtr4d
    cF
    df-rn
    syl6sseq
    @8
    @28
    sseqin2
    sylib
    @3
    @9
    @14
    simprr
    eqnetrd
    @18
    c0
    @29
    c0
    @17
    @8
    imadisj
    necon3bii
    sylibr
    @16
    @2
    @8
    @5
    wcel
    @18
    cJ
    ccld
    cfv
    wcel
    @25
    @16
    @6
    @5
    @8
    cK
    @5
    inss2
    @26
    sseldi
    @8
    cF
    cJ
    cK
    cnclima
    syl2anc
    connclo
    @16
    @2
    @21
    cY
    cF
    wf
    @22
    @21
    wceq
    @25
    cF
    cJ
    cK
    @21
    cY
    @23
    cnconn.2
    cnf
    @21
    cY
    cF
    fdm
    3syl
    @16
    @1
    cX
    cY
    cF
    wf
    @22
    cX
    wceq
    @33
    cX
    cY
    cF
    fof
    cX
    cY
    cF
    fdm
    3syl
    3eqtr2d
    imaeq2d
    @16
    @1
    @8
    cY
    wss
    @19
    @8
    wceq
    @33
    @32
    cX
    cY
    @8
    cF
    foimacnv
    syl2anc
    @16
    @1
    @20
    cY
    wceq
    @33
    cX
    cY
    cF
    foima
    syl
    3eqtr3d
    expr
    syl5bir
    orrd
    @8
    c0
    cY
    vx
    vex
    elpr
    sylibr
    ex
    ssrdv
    cK
    cY
    cnconn.2
    isconn2
    sylanbrc
end
