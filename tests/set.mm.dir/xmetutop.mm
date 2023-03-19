include "c0.mm"
include "wne.mm"
include "cxmt.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "cmetu.mm"
include "cutop.mm"
include "cbl.mm"
include "crn.mm"
include "ctg.mm"
include "cmopn.mm"
include "cpsmet.mm"
include "wceq.mm"
include "xmetpsmet.mm"
include "psmetutop.mm"
include "sylan2.mm"
include "eqid.mm"
include "mopnval.mm"
include "adantl.mm"
include "eqtr4d.mm"

theorem xmetutop
  let cD: class D
  let cX: class X
  let va: setvar a
  let vb: setvar b
  let vd: setvar d
  let ve: setvar e
  let vv: setvar v
  let vx: setvar x


  assert |- ( ( X =/= (/) /\ D e. ( *Met ` X ) ) -> ( unifTop ` ( metUnif ` D ) ) = ( MetOpen ` D ) )

  proof
    cX
    c0
    wne
    #
    cD
    cX
    cxmt
    cfv
    wcel
    #
    wa
    cD
    cmetu
    cfv
    cutop
    cfv
    #
    cD
    cbl
    cfv
    crn
    ctg
    cfv
    #
    cD
    cmopn
    cfv
    #
    @1
    @0
    cD
    cX
    cpsmet
    cfv
    wcel
    @2
    @3
    wceq
    cD
    cX
    xmetpsmet
    cD
    cX
    psmetutop
    sylan2
    @1
    @4
    @3
    wceq
    @0
    cD
    @4
    cX
    @4
    eqid
    mopnval
    adantl
    eqtr4d
end
