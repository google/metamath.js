include "cpsmet.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "cxp.mm"
include "cpw.mm"
include "crp.mm"
include "ccnv.mm"
include "cc0.mm"
include "cv.mm"
include "cico.mm"
include "co.mm"
include "cima.mm"
include "cmpt.mm"
include "crn.mm"
include "wral.mm"
include "wss.mm"
include "cdm.mm"
include "cnvimass.mm"
include "cxr.mm"
include "wf.mm"
include "wceq.mm"
include "psmetf.mm"
include "fdm.mm"
include "syl.mm"
include "syl5sseq.mm"
include "ad2antrr.mm"
include "wb.mm"
include "cvv.mm"
include "cnvexg.mm"
include "imaexg.mm"
include "elpwg.mm"
include "3syl.mm"
include "mpbird.mm"
include "ralrimiva.mm"
include "eqid.mm"
include "rnmptss.mm"
include "syl5eqss.mm"
include "simpr.mm"
include "sseldd.mm"
include "elpwid.mm"

theorem metustss
  let cA: class A
  let cD: class D
  let cF: class F
  let cX: class X
  let va: setvar a
  let cB: class B
  let vb: setvar b
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
  assert |- ( ( D e. ( PsMet ` X ) /\ A e. F ) -> A C_ ( X X. X ) )

  proof
    cD
    cX
    cpsmet
    cfv
    #
    wcel
    #
    cA
    cF
    wcel
    #
    wa
    #
    cA
    cX
    cX
    cxp
    #
    @3
    cF
    @4
    cpw
    #
    cA
    @3
    cF
    va
    crp
    cD
    ccnv
    #
    cc0
    va
    cv
    #
    cico
    co
    #
    cima
    #
    cmpt
    #
    crn
    #
    @5
    metust.1
    @3
    @9
    @5
    wcel
    #
    va
    crp
    wral
    @11
    @5
    wss
    @3
    @12
    va
    crp
    @3
    @7
    crp
    wcel
    #
    wa
    @12
    @9
    @4
    wss
    #
    @1
    @14
    @2
    @13
    @1
    cD
    cdm
    #
    @9
    @4
    cD
    @8
    cnvimass
    @1
    @4
    cxr
    cD
    wf
    @15
    @4
    wceq
    cD
    cX
    psmetf
    @4
    cxr
    cD
    fdm
    syl
    syl5sseq
    ad2antrr
    @1
    @12
    @14
    wb
    #
    @2
    @13
    @1
    @6
    cvv
    wcel
    @9
    cvv
    wcel
    @16
    cD
    @0
    cnvexg
    @6
    @8
    cvv
    imaexg
    @9
    @4
    cvv
    elpwg
    3syl
    ad2antrr
    mpbird
    ralrimiva
    va
    crp
    @9
    @5
    @10
    @10
    eqid
    rnmptss
    syl
    syl5eqss
    @1
    @2
    simpr
    sseldd
    elpwid
end
