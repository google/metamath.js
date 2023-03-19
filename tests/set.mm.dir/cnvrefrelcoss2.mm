include "ccoss.mm"
include "wcnvrefrel.mm"
include "cid.mm"
include "cdm.mm"
include "crn.mm"
include "cxp.mm"
include "cin.mm"
include "wss.mm"
include "wrel.mm"
include "relcoss.mm"
include "dfcnvrefrel2.mm"
include "mpbiran2.mm"
include "cossssid.mm"
include "bitr4i.mm"

theorem cnvrefrelcoss2
  let cR: class R


  assert |- ( CnvRefRel ,~ R <-> ,~ R C_ _I )

  proof
    cR
    ccoss
    #
    wcnvrefrel
    #
    @0
    cid
    @0
    cdm
    @0
    crn
    cxp
    cin
    wss
    #
    @0
    cid
    wss
    @1
    @2
    @0
    wrel
    cR
    relcoss
    @0
    dfcnvrefrel2
    mpbiran2
    cR
    cossssid
    bitr4i
end
