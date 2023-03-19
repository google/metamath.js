include "wfun.mm"
include "crn.mm"
include "wcel.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "cdm.mm"
include "wrex.mm"
include "wfn.mm"
include "wb.mm"
include "funfn.mm"
include "fvelrnb.mm"
include "sylbi.mm"
include "eqcom.mm"
include "rexbii.mm"
include "syl6bbr.mm"

theorem elrnrexdmb
  let vx: setvar x
  let cF: class F
  let cY: class Y
  let vy: setvar y

  disjoint F x
  disjoint Y x
  disjoint F y
  disjoint x y
  disjoint Y y
  assert |- ( Fun F -> ( Y e. ran F <-> E. x e. dom F Y = ( F ` x ) ) )

  proof
    cF
    wfun
    #
    cY
    cF
    crn
    wcel
    #
    vx
    cv
    cF
    cfv
    #
    cY
    wceq
    #
    vx
    cF
    cdm
    #
    wrex
    #
    cY
    @2
    wceq
    #
    vx
    @4
    wrex
    @0
    cF
    @4
    wfn
    @1
    @5
    wb
    cF
    funfn
    vx
    @4
    cY
    cF
    fvelrnb
    sylbi
    @6
    @3
    vx
    @4
    cY
    @2
    eqcom
    rexbii
    syl6bbr
end
