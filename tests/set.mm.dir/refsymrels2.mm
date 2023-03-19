include "crefrels.mm"
include "csymrels.mm"
include "cin.mm"
include "cid.mm"
include "cv.mm"
include "cdm.mm"
include "crn.mm"
include "cxp.mm"
include "wss.mm"
include "crels.mm"
include "crab.mm"
include "ccnv.mm"
include "wa.mm"
include "cres.mm"
include "dfrefrels2.mm"
include "dfsymrels2.mm"
include "ineq12i.mm"
include "inrab.mm"
include "symrefref2.mm"
include "pm5.32ri.mm"
include "rabbii.mm"
include "3eqtri.mm"

theorem refsymrels2
  let vr: setvar r


  assert |- ( RefRels i^i SymRels ) = { r e. Rels | ( ( _I |` dom r ) C_ r /\ `' r C_ r ) }

  proof
    crefrels
    csymrels
    cin
    cid
    vr
    cv
    #
    cdm
    #
    @0
    crn
    cxp
    cin
    @0
    wss
    #
    vr
    crels
    crab
    #
    @0
    ccnv
    @0
    wss
    #
    vr
    crels
    crab
    #
    cin
    @2
    @4
    wa
    #
    vr
    crels
    crab
    cid
    @1
    cres
    @0
    wss
    #
    @4
    wa
    #
    vr
    crels
    crab
    crefrels
    @3
    csymrels
    @5
    vr
    dfrefrels2
    vr
    dfsymrels2
    ineq12i
    @2
    @4
    vr
    crels
    inrab
    @6
    @8
    vr
    crels
    @4
    @2
    @7
    @0
    symrefref2
    pm5.32ri
    rabbii
    3eqtri
end
