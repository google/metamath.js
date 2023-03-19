include "wfun.mm"
include "crn.mm"
include "cvv.mm"
include "cxp.mm"
include "wss.mm"
include "wa.mm"
include "cv.mm"
include "cdm.mm"
include "wcel.mm"
include "cfv.mm"
include "c1st.mm"
include "c2nd.mm"
include "cop.mm"
include "ccom.mm"
include "wceq.mm"
include "simplr.mm"
include "fvelrn.mm"
include "adantlr.mm"
include "sseldd.mm"
include "1st2ndb.mm"
include "sylib.mm"
include "fvco.mm"
include "opeq12d.mm"
include "eqtr4d.mm"

theorem opfv
  let vx: setvar x
  let cF: class F


  assert |- ( ( ( Fun F /\ ran F C_ ( _V X. _V ) ) /\ x e. dom F ) -> ( F ` x ) = <. ( ( 1st o. F ) ` x ) , ( ( 2nd o. F ) ` x ) >. )

  proof
    cF
    wfun
    #
    cF
    crn
    #
    cvv
    cvv
    cxp
    #
    wss
    #
    wa
    vx
    cv
    #
    cF
    cdm
    wcel
    #
    wa
    #
    @4
    cF
    cfv
    #
    @7
    c1st
    cfv
    #
    @7
    c2nd
    cfv
    #
    cop
    #
    @4
    c1st
    cF
    ccom
    cfv
    #
    @4
    c2nd
    cF
    ccom
    cfv
    #
    cop
    #
    @6
    @7
    @2
    wcel
    @7
    @10
    wceq
    @6
    @1
    @2
    @7
    @0
    @3
    @5
    simplr
    @0
    @5
    @7
    @1
    wcel
    @3
    @4
    cF
    fvelrn
    adantlr
    sseldd
    @7
    1st2ndb
    sylib
    @0
    @5
    @13
    @10
    wceq
    @3
    @0
    @5
    wa
    @11
    @8
    @12
    @9
    @4
    c1st
    cF
    fvco
    @4
    c2nd
    cF
    fvco
    opeq12d
    adantlr
    eqtr4d
end
