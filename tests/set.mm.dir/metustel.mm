include "wcel.mm"
include "crp.mm"
include "ccnv.mm"
include "cc0.mm"
include "cv.mm"
include "cico.mm"
include "co.mm"
include "cima.mm"
include "cmpt.mm"
include "crn.mm"
include "cpsmet.mm"
include "cfv.mm"
include "wceq.mm"
include "wrex.mm"
include "eleq2i.mm"
include "cvv.mm"
include "wi.mm"
include "elex.mm"
include "a1i.mm"
include "cnvexg.mm"
include "imaexg.mm"
include "eleq1a.mm"
include "3syl.mm"
include "rexlimdvw.mm"
include "wb.mm"
include "eqid.mm"
include "elrnmpt.mm"
include "pm5.21ndd.mm"
include "syl5bb.mm"

theorem metustel
  let cB: class B
  let cD: class D
  let cF: class F
  let cX: class X
  let va: setvar a
  assume metust.1: |- F = ran ( a e. RR+ |-> ( `' D " ( 0 [,) a ) ) )

  disjoint B a
  disjoint D a
  disjoint X a
  assert |- ( D e. ( PsMet ` X ) -> ( B e. F <-> E. a e. RR+ B = ( `' D " ( 0 [,) a ) ) ) )

  proof
    cB
    cF
    wcel
    cB
    va
    crp
    cD
    ccnv
    #
    cc0
    va
    cv
    cico
    co
    #
    cima
    #
    cmpt
    #
    crn
    #
    wcel
    #
    cD
    cX
    cpsmet
    cfv
    #
    wcel
    #
    cB
    @2
    wceq
    #
    va
    crp
    wrex
    #
    cF
    @4
    cB
    metust.1
    eleq2i
    @7
    cB
    cvv
    wcel
    #
    @5
    @9
    @5
    @10
    wi
    @7
    cB
    @4
    elex
    a1i
    @7
    @8
    @10
    va
    crp
    @7
    @0
    cvv
    wcel
    @2
    cvv
    wcel
    @8
    @10
    wi
    cD
    @6
    cnvexg
    @0
    @1
    cvv
    imaexg
    @2
    cvv
    cB
    eleq1a
    3syl
    rexlimdvw
    @10
    @5
    @9
    wb
    wi
    @7
    va
    crp
    @2
    cB
    @3
    cvv
    @3
    eqid
    elrnmpt
    a1i
    pm5.21ndd
    syl5bb
end
