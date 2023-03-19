include "c0.mm"
include "wne.mm"
include "cpsmet.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "cmetu.mm"
include "cxp.mm"
include "crp.mm"
include "ccnv.mm"
include "cc0.mm"
include "cv.mm"
include "cico.mm"
include "co.mm"
include "cima.mm"
include "cmpt.mm"
include "crn.mm"
include "cfg.mm"
include "cust.mm"
include "wceq.mm"
include "metuval.mm"
include "adantl.mm"
include "oveq2.mm"
include "imaeq2d.mm"
include "cbvmptv.mm"
include "rneqi.mm"
include "metust.mm"
include "eqeltrd.mm"

theorem metuust
  let cD: class D
  let cX: class X
  let va: setvar a
  let vb: setvar b


  assert |- ( ( X =/= (/) /\ D e. ( PsMet ` X ) ) -> ( metUnif ` D ) e. ( UnifOn ` X ) )

  proof
    cX
    c0
    wne
    #
    cD
    cX
    cpsmet
    cfv
    wcel
    #
    wa
    cD
    cmetu
    cfv
    #
    cX
    cX
    cxp
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
    cfg
    co
    #
    cX
    cust
    cfv
    @1
    @2
    @9
    wceq
    @0
    cD
    cX
    va
    metuval
    adantl
    cD
    @8
    cX
    vb
    @7
    vb
    crp
    @3
    cc0
    vb
    cv
    #
    cico
    co
    #
    cima
    #
    cmpt
    va
    vb
    crp
    @6
    @12
    @4
    @10
    wceq
    @5
    @11
    @3
    @4
    @10
    cc0
    cico
    oveq2
    imaeq2d
    cbvmptv
    rneqi
    metust
    eqeltrd
end
