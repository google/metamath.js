include "cv.mm"
include "cid.mm"
include "cdm.mm"
include "crn.mm"
include "cxp.mm"
include "cin.mm"
include "wss.mm"
include "crels.mm"
include "ccnvrefrels.mm"
include "dfcnvrefrels2.mm"
include "wceq.mm"
include "id.mm"
include "dmeq.mm"
include "rneq.mm"
include "xpeq12d.mm"
include "ineq2d.mm"
include "sseq12d.mm"
include "rabeqel.mm"

theorem elcnvrefrels2
  let cR: class R
  let vr: setvar r


  assert |- ( R e. CnvRefRels <-> ( R C_ ( _I i^i ( dom R X. ran R ) ) /\ R e. Rels ) )

  proof
    vr
    cv
    #
    cid
    @0
    cdm
    #
    @0
    crn
    #
    cxp
    #
    cin
    #
    wss
    cR
    cid
    cR
    cdm
    #
    cR
    crn
    #
    cxp
    #
    cin
    #
    wss
    vr
    crels
    ccnvrefrels
    cR
    vr
    dfcnvrefrels2
    @0
    cR
    wceq
    #
    @0
    cR
    @4
    @8
    @9
    id
    @9
    @3
    @7
    cid
    @9
    @1
    @5
    @2
    @6
    @0
    cR
    dmeq
    @0
    cR
    rneq
    xpeq12d
    ineq2d
    sseq12d
    rabeqel
end
