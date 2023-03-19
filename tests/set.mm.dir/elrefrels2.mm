include "cid.mm"
include "cv.mm"
include "cdm.mm"
include "crn.mm"
include "cxp.mm"
include "cin.mm"
include "wss.mm"
include "crels.mm"
include "crefrels.mm"
include "dfrefrels2.mm"
include "wceq.mm"
include "dmeq.mm"
include "rneq.mm"
include "xpeq12d.mm"
include "ineq2d.mm"
include "id.mm"
include "sseq12d.mm"
include "rabeqel.mm"

theorem elrefrels2
  let cR: class R
  let vr: setvar r


  assert |- ( R e. RefRels <-> ( ( _I i^i ( dom R X. ran R ) ) C_ R /\ R e. Rels ) )

  proof
    cid
    vr
    cv
    #
    cdm
    #
    @0
    crn
    #
    cxp
    #
    cin
    #
    @0
    wss
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
    cR
    wss
    vr
    crels
    crefrels
    cR
    vr
    dfrefrels2
    @0
    cR
    wceq
    #
    @4
    @8
    @0
    cR
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
    @9
    id
    sseq12d
    rabeqel
end
