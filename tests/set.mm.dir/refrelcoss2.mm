include "cid.mm"
include "ccoss.mm"
include "cdm.mm"
include "crn.mm"
include "cxp.mm"
include "cin.mm"
include "wss.mm"
include "wrel.mm"
include "wa.mm"
include "cv.mm"
include "wceq.mm"
include "wbr.mm"
include "wi.mm"
include "wral.mm"
include "refrelcoss3.mm"
include "idinxpss.mm"
include "anbi1i.mm"
include "mpbir.mm"

theorem refrelcoss2
  let cR: class R
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( _I i^i ( dom ,~ R X. ran ,~ R ) ) C_ ,~ R /\ Rel ,~ R )

  proof
    cid
    cR
    ccoss
    #
    cdm
    #
    @0
    crn
    #
    cxp
    cin
    @0
    wss
    #
    @0
    wrel
    #
    wa
    vx
    cv
    #
    vy
    cv
    #
    wceq
    @5
    @6
    @0
    wbr
    wi
    vy
    @2
    wral
    vx
    @1
    wral
    #
    @4
    wa
    vx
    vy
    cR
    refrelcoss3
    @3
    @7
    @4
    vx
    vy
    @1
    @2
    @0
    idinxpss
    anbi1i
    mpbir
end
