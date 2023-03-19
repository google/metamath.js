include "chlo.mm"
include "wcel.mm"
include "cba.mm"
include "cfv.mm"
include "cms.mm"
include "cca.mm"
include "clm.mm"
include "cdm.mm"
include "eqid.mm"
include "hlcmet.mm"
include "cmetcau.mm"
include "sylan.mm"

theorem hlcompl
  let cD: class D
  let cU: class U
  let cF: class F
  let cJ: class J
  assume hlcompl.1: |- D = ( IndMet ` U )
  assume hlcompl.2: |- J = ( MetOpen ` D )


  assert |- ( ( U e. CHilOLD /\ F e. ( Cau ` D ) ) -> F e. dom ( ~~>t ` J ) )

  proof
    cU
    chlo
    wcel
    cD
    cU
    cba
    cfv
    #
    cms
    cfv
    wcel
    cF
    cD
    cca
    cfv
    wcel
    cF
    cJ
    clm
    cfv
    cdm
    wcel
    cD
    cU
    @0
    @0
    eqid
    hlcompl.1
    hlcmet
    cD
    cF
    cJ
    @0
    hlcompl.2
    cmetcau
    sylan
end
