include "wceq.mm"
include "cv.mm"
include "cfv.mm"
include "wbr.mm"
include "cdm.mm"
include "cin.mm"
include "wral.mm"
include "copab.mm"
include "cofr.mm"
include "breq.mm"
include "ralbidv.mm"
include "opabbidv.mm"
include "df-ofr.mm"
include "3eqtr4g.mm"

theorem ofreq
  let cR: class R
  let cS: class S
  let vf: setvar f
  let vg: setvar g
  let vx: setvar x


  assert |- ( R = S -> oR R = oR S )

  proof
    cR
    cS
    wceq
    #
    vx
    cv
    #
    vf
    cv
    #
    cfv
    #
    @1
    vg
    cv
    #
    cfv
    #
    cR
    wbr
    #
    vx
    @2
    cdm
    @4
    cdm
    cin
    #
    wral
    #
    vf
    vg
    copab
    @3
    @5
    cS
    wbr
    #
    vx
    @7
    wral
    #
    vf
    vg
    copab
    cR
    cofr
    cS
    cofr
    @0
    @8
    @10
    vf
    vg
    @0
    @6
    @9
    vx
    @7
    @3
    @5
    cR
    cS
    breq
    ralbidv
    opabbidv
    vx
    cR
    vf
    vg
    df-ofr
    vx
    cS
    vf
    vg
    df-ofr
    3eqtr4g
end
