include "cmt.mm"
include "wcel.mm"
include "cme.mm"
include "cfv.mm"
include "cmopn.mm"
include "wceq.mm"
include "isms2.mm"
include "simprbi.mm"

theorem mstopn
  let cD: class D
  let cJ: class J
  let cK: class K
  let cX: class X
  let vf: setvar f
  let vx: setvar x
  assume isms.j: |- J = ( TopOpen ` K )
  assume isms.x: |- X = ( Base ` K )
  assume isms.d: |- D = ( ( dist ` K ) |` ( X X. X ) )


  assert |- ( K e. MetSp -> J = ( MetOpen ` D ) )

  proof
    cK
    cmt
    wcel
    cD
    cX
    cme
    cfv
    wcel
    cJ
    cD
    cmopn
    cfv
    wceq
    cD
    cJ
    cK
    cX
    isms.j
    isms.x
    isms.d
    isms2
    simprbi
end
