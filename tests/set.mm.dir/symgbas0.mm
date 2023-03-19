include "c0.mm"
include "cv.mm"
include "wf1o.mm"
include "cab.mm"
include "wceq.mm"
include "csymg.mm"
include "cfv.mm"
include "cbs.mm"
include "csn.mm"
include "eqid.mm"
include "f1o00.mm"
include "mpbiran2.mm"
include "abbii.mm"
include "symgbas.mm"
include "df-sn.mm"
include "3eqtr4i.mm"

theorem symgbas0
  let vf: setvar f


  assert |- ( Base ` ( SymGrp ` (/) ) ) = { (/) }

  proof
    c0
    c0
    vf
    cv
    #
    wf1o
    #
    vf
    cab
    @0
    c0
    wceq
    #
    vf
    cab
    c0
    csymg
    cfv
    #
    cbs
    cfv
    #
    c0
    csn
    @1
    @2
    vf
    @1
    @2
    c0
    c0
    wceq
    c0
    eqid
    c0
    @0
    f1o00
    mpbiran2
    abbii
    vf
    c0
    @4
    @3
    @3
    eqid
    @4
    eqid
    symgbas
    vf
    c0
    df-sn
    3eqtr4i
end
