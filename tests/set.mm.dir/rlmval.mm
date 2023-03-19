include "cvv.mm"
include "wcel.mm"
include "crglmod.mm"
include "cfv.mm"
include "cbs.mm"
include "csra.mm"
include "wceq.mm"
include "cv.mm"
include "fveq2.mm"
include "fveq12d.mm"
include "df-rgmod.mm"
include "fvex.mm"
include "fvmpt.mm"
include "wn.mm"
include "c0.mm"
include "0fv.mm"
include "eqcomi.mm"
include "fvprc.mm"
include "fveq1d.mm"
include "3eqtr4a.mm"
include "pm2.61i.mm"

theorem rlmval
  let cW: class W
  let va: setvar a


  assert |- ( ringLMod ` W ) = ( ( subringAlg ` W ) ` ( Base ` W ) )

  proof
    cW
    cvv
    wcel
    #
    cW
    crglmod
    cfv
    #
    cW
    cbs
    cfv
    #
    cW
    csra
    cfv
    #
    cfv
    #
    wceq
    va
    cW
    va
    cv
    #
    cbs
    cfv
    #
    @5
    csra
    cfv
    #
    cfv
    @4
    cvv
    crglmod
    @5
    cW
    wceq
    @6
    @2
    @7
    @3
    @5
    cW
    csra
    fveq2
    @5
    cW
    cbs
    fveq2
    fveq12d
    va
    df-rgmod
    @2
    @3
    fvex
    fvmpt
    @0
    wn
    #
    c0
    @2
    c0
    cfv
    #
    @1
    @4
    @9
    c0
    @2
    0fv
    eqcomi
    cW
    crglmod
    fvprc
    @8
    @2
    @3
    c0
    cW
    csra
    fvprc
    fveq1d
    3eqtr4a
    pm2.61i
end
