include "cxmt.mm"
include "cfv.mm"
include "wcel.mm"
include "cbs.mm"
include "wceq.mm"
include "cds.mm"
include "cmopn.mm"
include "ctopn.mm"
include "cnx.mm"
include "cop.mm"
include "cpr.mm"
include "eqid.mm"
include "tmslem.mm"
include "simp2d.mm"

theorem tmsds
  let cD: class D
  let cK: class K
  let cX: class X
  assume tmsbas.k: |- K = ( toMetSp ` D )


  assert |- ( D e. ( *Met ` X ) -> D = ( dist ` K ) )

  proof
    cD
    cX
    cxmt
    cfv
    wcel
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
    cD
    cmopn
    cfv
    cK
    ctopn
    cfv
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
    @0
    eqid
    tmsbas.k
    tmslem
    simp2d
end
