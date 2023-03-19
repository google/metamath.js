include "ccoss.mm"
include "cid.mm"
include "wss.mm"
include "cdm.mm"
include "crn.mm"
include "cxp.mm"
include "cin.mm"
include "wceq.mm"
include "iss2.mm"
include "wrel.mm"
include "refrelcoss2.mm"
include "simpli.mm"
include "eqss.mm"
include "mpbiran2.mm"
include "bitri.mm"

theorem cossssid
  let cR: class R


  assert |- ( ,~ R C_ _I <-> ,~ R C_ ( _I i^i ( dom ,~ R X. ran ,~ R ) ) )

  proof
    cR
    ccoss
    #
    cid
    wss
    @0
    cid
    @0
    cdm
    @0
    crn
    cxp
    cin
    #
    wceq
    #
    @0
    @1
    wss
    #
    @0
    iss2
    @2
    @3
    @1
    @0
    wss
    #
    @4
    @0
    wrel
    cR
    refrelcoss2
    simpli
    @0
    @1
    eqss
    mpbiran2
    bitri
end
