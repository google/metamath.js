include "wfun.mm"
include "crn.mm"
include "wcel.mm"
include "cv.mm"
include "wceq.mm"
include "wrex.mm"
include "cfv.mm"
include "cdm.mm"
include "wa.mm"
include "eqidd.mm"
include "ancli.mm"
include "adantl.mm"
include "eqeq2.mm"
include "rspcev.mm"
include "syl.mm"
include "ex.mm"
include "wfn.mm"
include "wb.mm"
include "funfn.mm"
include "rexrn.mm"
include "sylbi.mm"
include "sylibd.mm"

theorem elrnrexdm
  let vx: setvar x
  let cF: class F
  let cY: class Y
  let vy: setvar y

  disjoint F x
  disjoint Y x
  disjoint F y
  disjoint x y
  disjoint Y y
  assert |- ( Fun F -> ( Y e. ran F -> E. x e. dom F Y = ( F ` x ) ) )

  proof
    cF
    wfun
    #
    cY
    cF
    crn
    #
    wcel
    #
    cY
    vy
    cv
    #
    wceq
    #
    vy
    @1
    wrex
    #
    cY
    vx
    cv
    cF
    cfv
    #
    wceq
    #
    vx
    cF
    cdm
    #
    wrex
    #
    @0
    @2
    @5
    @0
    @2
    wa
    @2
    cY
    cY
    wceq
    #
    wa
    #
    @5
    @2
    @11
    @0
    @2
    @10
    @2
    cY
    eqidd
    ancli
    adantl
    @4
    @10
    vy
    cY
    @1
    @3
    cY
    cY
    eqeq2
    rspcev
    syl
    ex
    @0
    cF
    @8
    wfn
    @5
    @9
    wb
    cF
    funfn
    @4
    @7
    vy
    vx
    @8
    cF
    @3
    @6
    cY
    eqeq2
    rexrn
    sylbi
    sylibd
end
