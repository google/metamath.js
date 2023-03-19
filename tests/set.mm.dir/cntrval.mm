include "cvv.mm"
include "wcel.mm"
include "cfv.mm"
include "ccntr.mm"
include "wceq.mm"
include "cv.mm"
include "cbs.mm"
include "ccntz.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "fveq12d.mm"
include "df-cntr.mm"
include "fvex.mm"
include "fvmpt.mm"
include "eqcomd.mm"
include "wn.mm"
include "c0.mm"
include "0fv.mm"
include "fvprc.mm"
include "syl5eq.mm"
include "fveq1d.mm"
include "3eqtr4a.mm"
include "pm2.61i.mm"

theorem cntrval
  let cB: class B
  let cM: class M
  let cZ: class Z
  let vm: setvar m
  assume cntrval.b: |- B = ( Base ` M )
  assume cntrval.z: |- Z = ( Cntz ` M )


  assert |- ( Z ` B ) = ( Cntr ` M )

  proof
    cM
    cvv
    wcel
    #
    cB
    cZ
    cfv
    #
    cM
    ccntr
    cfv
    #
    wceq
    @0
    @2
    @1
    vm
    cM
    vm
    cv
    #
    cbs
    cfv
    #
    @3
    ccntz
    cfv
    #
    cfv
    @1
    cvv
    ccntr
    @3
    cM
    wceq
    #
    @4
    cB
    @5
    cZ
    @6
    @5
    cM
    ccntz
    cfv
    #
    cZ
    @3
    cM
    ccntz
    fveq2
    cntrval.z
    syl6eqr
    @6
    @4
    cM
    cbs
    cfv
    cB
    @3
    cM
    cbs
    fveq2
    cntrval.b
    syl6eqr
    fveq12d
    vm
    df-cntr
    cB
    cZ
    fvex
    fvmpt
    eqcomd
    @0
    wn
    #
    cB
    c0
    cfv
    c0
    @1
    @2
    cB
    0fv
    @8
    cB
    cZ
    c0
    @8
    cZ
    @7
    c0
    cntrval.z
    cM
    ccntz
    fvprc
    syl5eq
    fveq1d
    cM
    ccntr
    fvprc
    3eqtr4a
    pm2.61i
end
