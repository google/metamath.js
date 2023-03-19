include "cxmt.mm"
include "cfv.mm"
include "wcel.mm"
include "cmopn.mm"
include "ctopn.mm"
include "cbs.mm"
include "wceq.mm"
include "cds.mm"
include "cnx.mm"
include "cop.mm"
include "cpr.mm"
include "eqid.mm"
include "tmslem.mm"
include "simp3d.mm"
include "syl5eq.mm"

theorem tmstopn
  let cD: class D
  let cJ: class J
  let cK: class K
  let cX: class X
  assume tmsbas.k: |- K = ( toMetSp ` D )
  assume tmstopn.j: |- J = ( MetOpen ` D )


  assert |- ( D e. ( *Met ` X ) -> J = ( TopOpen ` K ) )

  proof
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
    #
    cK
    ctopn
    cfv
    #
    tmstopn.j
    @0
    cX
    cK
    cbs
    cfv
    wceq
    cD
    cK
    cds
    cfv
    wceq
    @1
    @2
    wceq
    cD
    cK
    cnx
    cbs
    cfv
    cX
    cop
    cnx
    cds
    cfv
    cD
    cop
    cpr
    #
    cX
    @3
    eqid
    tmsbas.k
    tmslem
    simp3d
    syl5eq
end
