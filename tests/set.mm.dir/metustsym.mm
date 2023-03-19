include "cpsmet.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "ccnv.mm"
include "cxp.mm"
include "wss.mm"
include "metustss.mm"
include "cnvss.mm"
include "cnvxp.mm"
include "syl6sseq.mm"
include "syl.mm"
include "cv.mm"
include "wbr.mm"
include "wb.mm"
include "cop.mm"
include "cc0.mm"
include "cico.mm"
include "co.mm"
include "cima.mm"
include "wceq.mm"
include "crp.mm"
include "simp-4l.mm"
include "simpr1r.mm"
include "3anassrs.mm"
include "simpr1l.mm"
include "psmetsym.mm"
include "syl3anc.mm"
include "df-ov.mm"
include "3eqtr3g.mm"
include "eleq1d.mm"
include "wfun.mm"
include "cdm.mm"
include "cxr.mm"
include "wf.mm"
include "psmetf.mm"
include "ffun.mm"
include "3syl.mm"
include "simpllr.mm"
include "ancomd.mm"
include "opelxpi.mm"
include "fdm.mm"
include "eleqtrrd.mm"
include "fvimacnv.mm"
include "syl2anc.mm"
include "3bitr3d.mm"
include "simpr.mm"
include "eleq2d.mm"
include "3bitr4d.mm"
include "wrex.mm"
include "cmpt.mm"
include "crn.mm"
include "eqid.mm"
include "elrnmpt.mm"
include "ibi.mm"
include "eleq2s.mm"
include "ad2antlr.mm"
include "r19.29a.mm"
include "df-br.mm"
include "vex.mm"
include "opelcnv.mm"
include "bitri.mm"
include "3bitr4g.mm"
include "3impb.mm"
include "eqbrrdva.mm"

theorem metustsym
  let cA: class A
  let cD: class D
  let cF: class F
  let cX: class X
  let va: setvar a
  let cB: class B
  let vb: setvar b
  let vp: setvar p
  let vq: setvar q
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume metust.1: |- F = ran ( a e. RR+ |-> ( `' D " ( 0 [,) a ) ) )

  disjoint D a
  disjoint X a
  disjoint A a
  disjoint F a
  disjoint B a
  disjoint a b
  disjoint A b
  disjoint B b
  disjoint D b
  disjoint F b
  disjoint X b
  disjoint a p
  disjoint a q
  disjoint b p
  disjoint b q
  disjoint p q
  disjoint A p
  disjoint A q
  disjoint a x
  disjoint p x
  disjoint D p
  disjoint q x
  disjoint D q
  disjoint D x
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint p y
  disjoint p z
  disjoint F p
  disjoint q y
  disjoint q z
  disjoint F q
  disjoint x y
  disjoint x z
  disjoint F x
  disjoint y z
  disjoint F y
  disjoint F z
  disjoint X p
  disjoint X q
  disjoint X x
  disjoint X y
  disjoint X z
  assert |- ( ( D e. ( PsMet ` X ) /\ A e. F ) -> `' A = A )

  proof
    cD
    cX
    cpsmet
    cfv
    wcel
    #
    cA
    cF
    wcel
    #
    wa
    #
    vp
    vq
    cA
    ccnv
    #
    cA
    cX
    cX
    @2
    cA
    cX
    cX
    cxp
    #
    wss
    #
    @3
    @4
    wss
    cA
    cD
    cF
    cX
    va
    metust.1
    metustss
    #
    @5
    @3
    @4
    ccnv
    @4
    cA
    @4
    cnvss
    cX
    cX
    cnvxp
    syl6sseq
    syl
    @6
    @2
    vp
    cv
    #
    cX
    wcel
    #
    vq
    cv
    #
    cX
    wcel
    #
    @7
    @9
    @3
    wbr
    #
    @7
    @9
    cA
    wbr
    #
    wb
    @2
    @8
    @10
    wa
    #
    wa
    #
    @9
    @7
    cop
    #
    cA
    wcel
    #
    @7
    @9
    cop
    #
    cA
    wcel
    #
    @11
    @12
    @14
    cA
    cD
    ccnv
    cc0
    va
    cv
    #
    cico
    co
    #
    cima
    #
    wceq
    #
    @16
    @18
    wb
    va
    crp
    @14
    @19
    crp
    wcel
    #
    wa
    #
    @22
    wa
    #
    @15
    @21
    wcel
    #
    @17
    @21
    wcel
    #
    @16
    @18
    @25
    @15
    cD
    cfv
    #
    @20
    wcel
    #
    @17
    cD
    cfv
    #
    @20
    wcel
    #
    @26
    @27
    @25
    @28
    @30
    @20
    @25
    @9
    @7
    cD
    co
    #
    @7
    @9
    cD
    co
    #
    @28
    @30
    @25
    @0
    @10
    @8
    @32
    @33
    wceq
    @0
    @1
    @13
    @23
    @22
    simp-4l
    #
    @2
    @13
    @23
    @22
    @10
    @8
    @10
    @23
    @22
    @2
    simpr1r
    3anassrs
    @2
    @13
    @23
    @22
    @8
    @8
    @10
    @23
    @22
    @2
    simpr1l
    3anassrs
    @9
    @7
    cD
    cX
    psmetsym
    syl3anc
    @9
    @7
    cD
    df-ov
    @7
    @9
    cD
    df-ov
    3eqtr3g
    eleq1d
    @25
    cD
    wfun
    #
    @15
    cD
    cdm
    #
    wcel
    @29
    @26
    wb
    @25
    @0
    @4
    cxr
    cD
    wf
    #
    @35
    @34
    cD
    cX
    psmetf
    #
    @4
    cxr
    cD
    ffun
    3syl
    #
    @25
    @15
    @4
    @36
    @25
    @10
    @8
    wa
    @15
    @4
    wcel
    @25
    @8
    @10
    @2
    @13
    @23
    @22
    simpllr
    #
    ancomd
    @9
    @7
    cX
    cX
    opelxpi
    syl
    @25
    @0
    @37
    @36
    @4
    wceq
    @34
    @38
    @4
    cxr
    cD
    fdm
    3syl
    #
    eleqtrrd
    @15
    @20
    cD
    fvimacnv
    syl2anc
    @25
    @35
    @17
    @36
    wcel
    @31
    @27
    wb
    @39
    @25
    @17
    @4
    @36
    @25
    @13
    @17
    @4
    wcel
    @40
    @7
    @9
    cX
    cX
    opelxpi
    syl
    @41
    eleqtrrd
    @17
    @20
    cD
    fvimacnv
    syl2anc
    3bitr3d
    @25
    cA
    @21
    @15
    @24
    @22
    simpr
    #
    eleq2d
    @25
    cA
    @21
    @17
    @42
    eleq2d
    3bitr4d
    @1
    @22
    va
    crp
    wrex
    #
    @0
    @13
    @43
    cA
    va
    crp
    @21
    cmpt
    #
    crn
    #
    cF
    cA
    @45
    wcel
    @43
    va
    crp
    @21
    cA
    @44
    @45
    @44
    eqid
    elrnmpt
    ibi
    metust.1
    eleq2s
    ad2antlr
    r19.29a
    @11
    @17
    @3
    wcel
    @16
    @7
    @9
    @3
    df-br
    @7
    @9
    cA
    vp
    vex
    vq
    vex
    opelcnv
    bitri
    @7
    @9
    cA
    df-br
    3bitr4g
    3impb
    eqbrrdva
end
