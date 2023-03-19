include "wcel.mm"
include "cv.mm"
include "cfin3.mm"
include "cdif.mm"
include "wo.mm"
include "cpw.mm"
include "wral.mm"
include "com.mm"
include "cwdom.mm"
include "wbr.mm"
include "wn.mm"
include "wfo.mm"
include "wex.mm"
include "c0.mm"
include "wne.mm"
include "wb.mm"
include "peano1.mm"
include "ne0i.mm"
include "brwdomn0.mm"
include "mp2b.mm"
include "wrex.mm"
include "ccnv.mm"
include "crn.mm"
include "cima.mm"
include "cvv.mm"
include "wf.mm"
include "vex.mm"
include "fof.mm"
include "dmfex.mm"
include "sylancr.mm"
include "cdm.mm"
include "cnvimass.mm"
include "wceq.mm"
include "fdm.mm"
include "syl.mm"
include "syl5sseq.mm"
include "sselpwd.mm"
include "cres.mm"
include "ccom.mm"
include "wfun.mm"
include "wf1.mm"
include "wf1o.mm"
include "fin1a2lem4.mm"
include "f1cnv.mm"
include "f1ofo.mm"
include "fofun.mm"
include "ax-mp.mm"
include "resex.mm"
include "cofunexg.mm"
include "mp2an.mm"
include "wss.mm"
include "fores.mm"
include "sylancl.mm"
include "f1f.mm"
include "frn.mm"
include "foimacnv.mm"
include "mpan2.mm"
include "foeq3.mm"
include "mpbid.mm"
include "foco.mm"
include "fowdom.mm"
include "cnvex.mm"
include "imaex.mm"
include "isfin3-2.mm"
include "con2bii.mm"
include "sylib.mm"
include "fin1a2lem6.mm"
include "f1ocnv.mm"
include "difss.mm"
include "syl5sseqr.mm"
include "syl2anc.mm"
include "funcnvcnv.mm"
include "imadif.mm"
include "3syl.mm"
include "imaeq2d.mm"
include "fimacnv.mm"
include "difeq1d.mm"
include "3eqtr3rd.mm"
include "difexg.mm"
include "con2bid.mm"
include "wa.mm"
include "eleq1.mm"
include "difeq2.mm"
include "eleq1d.mm"
include "orbi12d.mm"
include "notbid.mm"
include "ioran.mm"
include "syl6bb.mm"
include "rspcev.mm"
include "syl12anc.mm"
include "rexnal.mm"
include "exlimiv.mm"
include "sylbi.mm"
include "con2i.mm"
include "syl5ibr.mm"
include "imp.mm"

theorem fin1a2lem7
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cS: class S
  let cE: class E
  let cV: class V
  let va: setvar a
  let vf: setvar f
  let vb: setvar b
  assume fin1a2lem.b: |- E = ( x e. _om |-> ( 2o .o x ) )
  assume fin1a2lem.aa: |- S = ( x e. On |-> suc x )

  disjoint A y
  disjoint E y
  disjoint a x
  disjoint a f
  disjoint a y
  disjoint A a
  disjoint f y
  disjoint A f
  disjoint a b
  disjoint E a
  disjoint b y
  disjoint E b
  disjoint S a
  disjoint S b
  assert |- ( ( A e. V /\ A. y e. ~P A ( y e. Fin3 \/ ( A \ y ) e. Fin3 ) ) -> A e. Fin3 )

  proof
    cA
    cV
    wcel
    #
    vy
    cv
    #
    cfin3
    wcel
    #
    cA
    @1
    cdif
    #
    cfin3
    wcel
    #
    wo
    #
    vy
    cA
    cpw
    #
    wral
    #
    cA
    cfin3
    wcel
    #
    @7
    @8
    @0
    com
    cA
    cwdom
    wbr
    #
    wn
    @9
    @7
    @9
    cA
    com
    vf
    cv
    #
    wfo
    #
    vf
    wex
    #
    @7
    wn
    #
    c0
    com
    wcel
    com
    c0
    wne
    @9
    @12
    wb
    peano1
    com
    c0
    ne0i
    vf
    com
    cA
    brwdomn0
    mp2b
    @11
    @13
    vf
    @11
    @5
    wn
    #
    vy
    @6
    wrex
    #
    @13
    @11
    @10
    ccnv
    #
    cE
    crn
    #
    cima
    #
    @6
    wcel
    @18
    cfin3
    wcel
    #
    wn
    #
    cA
    @18
    cdif
    #
    cfin3
    wcel
    #
    wn
    #
    @15
    @11
    @18
    cA
    cvv
    @11
    @10
    cvv
    wcel
    cA
    com
    @10
    wf
    #
    cA
    cvv
    wcel
    #
    vf
    vex
    #
    cA
    com
    @10
    fof
    #
    cA
    com
    cvv
    @10
    dmfex
    sylancr
    #
    @11
    @10
    cdm
    #
    @18
    cA
    @10
    @17
    cnvimass
    #
    @11
    @24
    @29
    cA
    wceq
    @27
    cA
    com
    @10
    fdm
    syl
    #
    syl5sseq
    sselpwd
    @11
    com
    @18
    cwdom
    wbr
    #
    @20
    @11
    cE
    ccnv
    #
    @10
    @18
    cres
    #
    ccom
    #
    cvv
    wcel
    #
    @18
    com
    @35
    wfo
    #
    @32
    @33
    wfun
    #
    @34
    cvv
    wcel
    @36
    @17
    com
    @33
    wfo
    #
    @38
    com
    com
    cE
    wf1
    #
    @17
    com
    @33
    wf1o
    @39
    vx
    cE
    fin1a2lem.b
    fin1a2lem4
    #
    com
    com
    cE
    f1cnv
    @17
    com
    @33
    f1ofo
    mp2b
    #
    @17
    com
    @33
    fofun
    ax-mp
    @10
    @18
    @26
    resex
    @33
    @34
    cvv
    cofunexg
    mp2an
    @11
    @39
    @18
    @17
    @34
    wfo
    #
    @37
    @42
    @11
    @18
    @10
    @18
    cima
    #
    @34
    wfo
    #
    @43
    @11
    @10
    wfun
    #
    @18
    @29
    wss
    @45
    cA
    com
    @10
    fofun
    #
    @30
    @18
    @10
    fores
    sylancl
    @11
    @44
    @17
    wceq
    #
    @45
    @43
    wb
    @11
    @17
    com
    wss
    #
    @48
    @40
    com
    com
    cE
    wf
    @49
    @41
    com
    com
    cE
    f1f
    com
    com
    cE
    frn
    mp2b
    cA
    com
    @17
    @10
    foimacnv
    mpan2
    @44
    @17
    @18
    @34
    foeq3
    syl
    mpbid
    @18
    @17
    com
    @33
    @34
    foco
    sylancr
    @35
    cvv
    com
    @18
    fowdom
    sylancr
    @19
    @32
    @18
    cvv
    wcel
    @19
    @32
    wn
    wb
    @16
    @17
    @10
    @26
    cnvex
    imaex
    @18
    cvv
    isfin3-2
    ax-mp
    con2bii
    sylib
    @11
    com
    @21
    cwdom
    wbr
    #
    @23
    @11
    @33
    cS
    @17
    cres
    #
    ccnv
    #
    ccom
    #
    @10
    @21
    cres
    #
    ccom
    #
    cvv
    wcel
    #
    @21
    com
    @55
    wfo
    #
    @50
    @53
    wfun
    #
    @54
    cvv
    wcel
    @56
    com
    @17
    cdif
    #
    com
    @53
    wfo
    #
    @58
    @39
    @59
    @17
    @52
    wfo
    #
    @60
    @42
    @17
    @59
    @51
    wf1o
    @59
    @17
    @52
    wf1o
    @61
    vx
    cS
    cE
    fin1a2lem.b
    fin1a2lem.aa
    fin1a2lem6
    @17
    @59
    @51
    f1ocnv
    @59
    @17
    @52
    f1ofo
    mp2b
    @59
    @17
    com
    @33
    @52
    foco
    mp2an
    #
    @59
    com
    @53
    fofun
    ax-mp
    @10
    @21
    @26
    resex
    @53
    @54
    cvv
    cofunexg
    mp2an
    @11
    @60
    @21
    @59
    @54
    wfo
    #
    @57
    @62
    @11
    @21
    @10
    @21
    cima
    #
    @54
    wfo
    #
    @63
    @11
    @46
    @21
    @29
    wss
    @65
    @47
    @11
    cA
    @21
    @29
    cA
    @18
    difss
    @31
    syl5sseqr
    @21
    @10
    fores
    syl2anc
    @11
    @64
    @59
    wceq
    @65
    @63
    wb
    @11
    @10
    @16
    @59
    cima
    #
    cima
    #
    @10
    @16
    com
    cima
    #
    @18
    cdif
    #
    cima
    @59
    @64
    @11
    @66
    @69
    @10
    @11
    @46
    @16
    ccnv
    wfun
    @66
    @69
    wceq
    @47
    @10
    funcnvcnv
    com
    @17
    @16
    imadif
    3syl
    imaeq2d
    @11
    @59
    com
    wss
    @67
    @59
    wceq
    com
    @17
    difss
    cA
    com
    @59
    @10
    foimacnv
    mpan2
    @11
    @69
    @21
    @10
    @11
    @68
    cA
    @18
    @11
    @24
    @68
    cA
    wceq
    @27
    cA
    com
    @10
    fimacnv
    syl
    difeq1d
    imaeq2d
    3eqtr3rd
    @64
    @59
    @21
    @54
    foeq3
    syl
    mpbid
    @21
    @59
    com
    @53
    @54
    foco
    sylancr
    @55
    cvv
    com
    @21
    fowdom
    sylancr
    @11
    @22
    @50
    @11
    @25
    @21
    cvv
    wcel
    @22
    @50
    wn
    wb
    @28
    cA
    @18
    cvv
    difexg
    @21
    cvv
    isfin3-2
    3syl
    con2bid
    mpbid
    @14
    @20
    @23
    wa
    #
    vy
    @18
    @6
    @1
    @18
    wceq
    #
    @14
    @19
    @22
    wo
    #
    wn
    @70
    @71
    @5
    @72
    @71
    @2
    @19
    @4
    @22
    @1
    @18
    cfin3
    eleq1
    @71
    @3
    @21
    cfin3
    @1
    @18
    cA
    difeq2
    eleq1d
    orbi12d
    notbid
    @19
    @22
    ioran
    syl6bb
    rspcev
    syl12anc
    @5
    vy
    @6
    rexnal
    sylib
    exlimiv
    sylbi
    con2i
    cA
    cV
    isfin3-2
    syl5ibr
    imp
end
