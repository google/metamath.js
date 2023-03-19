include "wceq.mm"
include "cvv.mm"
include "cv.mm"
include "cdm.mm"
include "cfv.mm"
include "co.mm"
include "cmpt.mm"
include "cmpt2.mm"
include "cofc.mm"
include "oveq.mm"
include "mpteq2dv.mm"
include "mpt2eq3dv.mm"
include "df-ofc.mm"
include "3eqtr4g.mm"

theorem ofceq
  let cR: class R
  let cS: class S
  let vc: setvar c
  let vf: setvar f
  let vx: setvar x


  assert |- ( R = S -> oFC R = oFC S )

  proof
    cR
    cS
    wceq
    #
    vf
    vc
    cvv
    cvv
    vx
    vf
    cv
    #
    cdm
    #
    vx
    cv
    @1
    cfv
    #
    vc
    cv
    #
    cR
    co
    #
    cmpt
    #
    cmpt2
    vf
    vc
    cvv
    cvv
    vx
    @2
    @3
    @4
    cS
    co
    #
    cmpt
    #
    cmpt2
    cR
    cofc
    cS
    cofc
    @0
    vf
    vc
    cvv
    cvv
    @6
    @8
    @0
    vx
    @2
    @5
    @7
    @3
    @4
    cR
    cS
    oveq
    mpteq2dv
    mpt2eq3dv
    vx
    cR
    vf
    vc
    df-ofc
    vx
    cS
    vf
    vc
    df-ofc
    3eqtr4g
end
