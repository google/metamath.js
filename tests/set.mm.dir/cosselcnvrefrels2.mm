include "ccoss.mm"
include "ccnvrefrels.mm"
include "wcel.mm"
include "cid.mm"
include "cdm.mm"
include "crn.mm"
include "cxp.mm"
include "cin.mm"
include "wss.mm"
include "crels.mm"
include "wa.mm"
include "elcnvrefrels2.mm"
include "cossssid.mm"
include "anbi1i.mm"
include "bitr4i.mm"

theorem cosselcnvrefrels2
  let cR: class R


  assert |- ( ,~ R e. CnvRefRels <-> ( ,~ R C_ _I /\ ,~ R e. Rels ) )

  proof
    cR
    ccoss
    #
    ccnvrefrels
    wcel
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
    crels
    wcel
    #
    wa
    @0
    cid
    wss
    #
    @2
    wa
    @0
    elcnvrefrels2
    @3
    @1
    @2
    cR
    cossssid
    anbi1i
    bitr4i
end
