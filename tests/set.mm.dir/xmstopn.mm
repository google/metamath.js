include "cxme.mm"
include "wcel.mm"
include "ctps.mm"
include "cmopn.mm"
include "cfv.mm"
include "wceq.mm"
include "isxms.mm"
include "simprbi.mm"

theorem xmstopn
  let cD: class D
  let cJ: class J
  let cK: class K
  let cX: class X
  let vf: setvar f
  let vx: setvar x
  assume isms.j: |- J = ( TopOpen ` K )
  assume isms.x: |- X = ( Base ` K )
  assume isms.d: |- D = ( ( dist ` K ) |` ( X X. X ) )


  assert |- ( K e. *MetSp -> J = ( MetOpen ` D ) )

  proof
    cK
    cxme
    wcel
    cK
    ctps
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
    isxms
    simprbi
end
