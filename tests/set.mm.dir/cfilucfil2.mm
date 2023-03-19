include "c0.mm"
include "wne.mm"
include "cpsmet.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "cmetu.mm"
include "ccfilu.mm"
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
include "cfbas.mm"
include "wss.mm"
include "wrex.mm"
include "wral.mm"
include "wceq.mm"
include "metuval.mm"
include "adantl.mm"
include "fveq2d.mm"
include "eleq2d.mm"
include "oveq2.mm"
include "imaeq2d.mm"
include "cbvmptv.mm"
include "rneqi.mm"
include "cfilucfil.mm"
include "bitrd.mm"

theorem cfilucfil2
  let vx: setvar x
  let vy: setvar y
  let cC: class C
  let cD: class D
  let cX: class X
  let vb: setvar b
  let va: setvar a

  disjoint x y
  disjoint C x
  disjoint C y
  disjoint D x
  disjoint D y
  disjoint X x
  disjoint X y
  disjoint b x
  disjoint b y
  disjoint C b
  disjoint a b
  disjoint a x
  disjoint a y
  disjoint D a
  disjoint D b
  disjoint X a
  disjoint X b
  assert |- ( ( X =/= (/) /\ D e. ( PsMet ` X ) ) -> ( C e. ( CauFilU ` ( metUnif ` D ) ) <-> ( C e. ( fBas ` X ) /\ A. x e. RR+ E. y e. C ( D " ( y X. y ) ) C_ ( 0 [,) x ) ) ) )

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
    cC
    cD
    cmetu
    cfv
    #
    ccfilu
    cfv
    #
    wcel
    cC
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
    ccfilu
    cfv
    #
    wcel
    cC
    cX
    cfbas
    cfv
    wcel
    cD
    vy
    cv
    #
    @13
    cxp
    cima
    cc0
    vx
    cv
    cico
    co
    wss
    vy
    cC
    wrex
    vx
    crp
    wral
    wa
    @2
    @4
    @12
    cC
    @2
    @3
    @11
    ccfilu
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
    fveq2d
    eleq2d
    vx
    vy
    cC
    cD
    @10
    cX
    vb
    @9
    vb
    crp
    @5
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
    cfilucfil
    bitrd
end
