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
include "wss.mm"
include "wrex.mm"
include "wceq.mm"
include "metuval.mm"
include "adantl.mm"
include "eleq2d.mm"
include "cfbas.mm"
include "wb.mm"
include "oveq2.mm"
include "imaeq2d.mm"
include "cbvmptv.mm"
include "rneqi.mm"
include "metustfbas.mm"
include "elfg.mm"
include "syl.mm"
include "bitrd.mm"

theorem metuel
  let vw: setvar w
  let cD: class D
  let cV: class V
  let cX: class X
  let va: setvar a
  let ve: setvar e

  disjoint a w
  disjoint D a
  disjoint D w
  disjoint X a
  disjoint V w
  disjoint a e
  disjoint e w
  disjoint D e
  disjoint X e
  assert |- ( ( X =/= (/) /\ D e. ( PsMet ` X ) ) -> ( V e. ( metUnif ` D ) <-> ( V C_ ( X X. X ) /\ E. w e. ran ( a e. RR+ |-> ( `' D " ( 0 [,) a ) ) ) w C_ V ) ) )

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
    #
    cV
    cD
    cmetu
    cfv
    #
    wcel
    cV
    cX
    cX
    cxp
    #
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
    wcel
    #
    cV
    @4
    wss
    vw
    cv
    cV
    wss
    vw
    @10
    wrex
    wa
    #
    @2
    @3
    @11
    cV
    @1
    @3
    @11
    wceq
    @0
    cD
    cX
    va
    metuval
    adantl
    eleq2d
    @2
    @10
    @4
    cfbas
    cfv
    wcel
    @12
    @13
    wb
    cD
    @10
    cX
    ve
    @9
    ve
    crp
    @5
    cc0
    ve
    cv
    #
    cico
    co
    #
    cima
    #
    cmpt
    va
    ve
    crp
    @8
    @16
    @6
    @14
    wceq
    @7
    @15
    @5
    @6
    @14
    cc0
    cico
    oveq2
    imaeq2d
    cbvmptv
    rneqi
    metustfbas
    vw
    cV
    @10
    @4
    elfg
    syl
    bitrd
end
