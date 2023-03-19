include "cid.mm"
include "whe.mm"
include "cres.mm"
include "cxp.mm"
include "wss.mm"
include "cdm.mm"
include "crn.mm"
include "wrel.mm"
include "relres.mm"
include "relssdmrn.mm"
include "ax-mp.mm"
include "dmresi.mm"
include "eqimssi.mm"
include "rnresi.mm"
include "xpss12.mm"
include "mp2an.mm"
include "sstri.mm"
include "dfhe2.mm"
include "mpbir.mm"

theorem idhe
  let cA: class A


  assert |- _I hereditary A

  proof
    cA
    cid
    whe
    cid
    cA
    cres
    #
    cA
    cA
    cxp
    #
    wss
    @0
    @0
    cdm
    #
    @0
    crn
    #
    cxp
    #
    @1
    @0
    wrel
    @0
    @4
    wss
    cid
    cA
    relres
    @0
    relssdmrn
    ax-mp
    @2
    cA
    wss
    @3
    cA
    wss
    @4
    @1
    wss
    @2
    cA
    cA
    dmresi
    eqimssi
    @3
    cA
    cA
    rnresi
    eqimssi
    @2
    cA
    @3
    cA
    xpss12
    mp2an
    sstri
    cA
    cid
    dfhe2
    mpbir
end
