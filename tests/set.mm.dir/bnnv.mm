include "ccbn.mm"
include "wcel.mm"
include "cnv.mm"
include "cims.mm"
include "cfv.mm"
include "cba.mm"
include "cms.mm"
include "eqid.mm"
include "iscbn.mm"
include "simplbi.mm"

theorem bnnv
  let cU: class U


  assert |- ( U e. CBan -> U e. NrmCVec )

  proof
    cU
    ccbn
    wcel
    cU
    cnv
    wcel
    cU
    cims
    cfv
    #
    cU
    cba
    cfv
    #
    cms
    cfv
    wcel
    @0
    cU
    @1
    @1
    eqid
    @0
    eqid
    iscbn
    simplbi
end
