include "cxme.mm"
include "wcel.mm"
include "cme.mm"
include "cfv.mm"
include "wa.mm"
include "cxmt.mm"
include "cmopn.mm"
include "wceq.mm"
include "cmt.mm"
include "isxms2.mm"
include "anbi1i.mm"
include "isms.mm"
include "metxmet.mm"
include "pm4.71ri.mm"
include "an32.mm"
include "bitri.mm"
include "3bitr4i.mm"

theorem isms2
  let cD: class D
  let cJ: class J
  let cK: class K
  let cX: class X
  let vf: setvar f
  let vx: setvar x
  assume isms.j: |- J = ( TopOpen ` K )
  assume isms.x: |- X = ( Base ` K )
  assume isms.d: |- D = ( ( dist ` K ) |` ( X X. X ) )


  assert |- ( K e. MetSp <-> ( D e. ( Met ` X ) /\ J = ( MetOpen ` D ) ) )

  proof
    cK
    cxme
    wcel
    #
    cD
    cX
    cme
    cfv
    wcel
    #
    wa
    cD
    cX
    cxmt
    cfv
    wcel
    #
    cJ
    cD
    cmopn
    cfv
    wceq
    #
    wa
    #
    @1
    wa
    #
    cK
    cmt
    wcel
    @1
    @3
    wa
    #
    @0
    @4
    @1
    cD
    cJ
    cK
    cX
    isms.j
    isms.x
    isms.d
    isxms2
    anbi1i
    cD
    cJ
    cK
    cX
    isms.j
    isms.x
    isms.d
    isms
    @6
    @2
    @1
    wa
    #
    @3
    wa
    @5
    @1
    @7
    @3
    @1
    @2
    cD
    cX
    metxmet
    pm4.71ri
    anbi1i
    @2
    @1
    @3
    an32
    bitri
    3bitr4i
end
