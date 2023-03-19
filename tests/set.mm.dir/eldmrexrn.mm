include "wfun.mm"
include "cdm.mm"
include "wcel.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "crn.mm"
include "wrex.mm"
include "wa.mm"
include "fvelrn.mm"
include "eqid.mm"
include "eqeq1.mm"
include "rspcev.mm"
include "sylancl.mm"
include "ex.mm"

theorem eldmrexrn
  let vx: setvar x
  let cF: class F
  let cY: class Y
  let vy: setvar y

  disjoint F x
  disjoint Y x
  disjoint F y
  disjoint x y
  disjoint Y y
  assert |- ( Fun F -> ( Y e. dom F -> E. x e. ran F x = ( F ` Y ) ) )

  proof
    cF
    wfun
    #
    cY
    cF
    cdm
    wcel
    #
    vx
    cv
    #
    cY
    cF
    cfv
    #
    wceq
    #
    vx
    cF
    crn
    #
    wrex
    #
    @0
    @1
    wa
    @3
    @5
    wcel
    @3
    @3
    wceq
    #
    @6
    cY
    cF
    fvelrn
    @3
    eqid
    @4
    @7
    vx
    @3
    @5
    @2
    @3
    @3
    eqeq1
    rspcev
    sylancl
    ex
end
