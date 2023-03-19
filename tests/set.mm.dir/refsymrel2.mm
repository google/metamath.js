include "wrefrel.mm"
include "wsymrel.mm"
include "wa.mm"
include "cid.mm"
include "cdm.mm"
include "crn.mm"
include "cxp.mm"
include "cin.mm"
include "wss.mm"
include "ccnv.mm"
include "wrel.mm"
include "cres.mm"
include "w3a.mm"
include "dfrefrel2.mm"
include "dfsymrel2.mm"
include "anbi12i.mm"
include "anandi3r.mm"
include "3anan32.mm"
include "3bitr2i.mm"
include "symrefref2.mm"
include "pm5.32ri.mm"
include "anbi1i.mm"
include "bitri.mm"

theorem refsymrel2
  let cR: class R


  assert |- ( ( RefRel R /\ SymRel R ) <-> ( ( ( _I |` dom R ) C_ R /\ `' R C_ R ) /\ Rel R ) )

  proof
    cR
    wrefrel
    #
    cR
    wsymrel
    #
    wa
    #
    cid
    cR
    cdm
    #
    cR
    crn
    cxp
    cin
    cR
    wss
    #
    cR
    ccnv
    cR
    wss
    #
    wa
    #
    cR
    wrel
    #
    wa
    #
    cid
    @3
    cres
    cR
    wss
    #
    @5
    wa
    #
    @7
    wa
    @2
    @4
    @7
    wa
    #
    @5
    @7
    wa
    #
    wa
    @4
    @7
    @5
    w3a
    @8
    @0
    @11
    @1
    @12
    cR
    dfrefrel2
    cR
    dfsymrel2
    anbi12i
    @4
    @7
    @5
    anandi3r
    @4
    @7
    @5
    3anan32
    3bitr2i
    @6
    @10
    @7
    @5
    @4
    @9
    cR
    symrefref2
    pm5.32ri
    anbi1i
    bitri
end
