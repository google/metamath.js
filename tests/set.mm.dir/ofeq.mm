include "wceq.mm"
include "cvv.mm"
include "cv.mm"
include "cdm.mm"
include "cin.mm"
include "cfv.mm"
include "co.mm"
include "cmpt.mm"
include "cmpt2.mm"
include "cof.mm"
include "wcel.mm"
include "w3a.mm"
include "simp1.mm"
include "oveqd.mm"
include "mpteq2dv.mm"
include "mpt2eq3dva.mm"
include "df-of.mm"
include "3eqtr4g.mm"

theorem ofeq
  let cR: class R
  let cS: class S
  let vf: setvar f
  let vg: setvar g
  let vx: setvar x


  assert |- ( R = S -> oF R = oF S )

  proof
    cR
    cS
    wceq
    #
    vf
    vg
    cvv
    cvv
    vx
    vf
    cv
    #
    cdm
    vg
    cv
    #
    cdm
    cin
    #
    vx
    cv
    #
    @1
    cfv
    #
    @4
    @2
    cfv
    #
    cR
    co
    #
    cmpt
    #
    cmpt2
    vf
    vg
    cvv
    cvv
    vx
    @3
    @5
    @6
    cS
    co
    #
    cmpt
    #
    cmpt2
    cR
    cof
    cS
    cof
    @0
    vf
    vg
    cvv
    cvv
    @8
    @10
    @0
    @1
    cvv
    wcel
    #
    @2
    cvv
    wcel
    #
    w3a
    #
    vx
    @3
    @7
    @9
    @13
    cR
    cS
    @5
    @6
    @0
    @11
    @12
    simp1
    oveqd
    mpteq2dv
    mpt2eq3dva
    vx
    cR
    vf
    vg
    df-of
    vx
    cS
    vf
    vg
    df-of
    3eqtr4g
end
