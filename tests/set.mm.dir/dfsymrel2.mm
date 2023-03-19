include "wsymrel.mm"
include "cdm.mm"
include "crn.mm"
include "cxp.mm"
include "cin.mm"
include "ccnv.mm"
include "wss.mm"
include "wrel.mm"
include "wa.mm"
include "df-symrel.mm"
include "wceq.mm"
include "dfrel6.mm"
include "biimpi.mm"
include "cnveqd.mm"
include "sseq12d.mm"
include "pm5.32ri.mm"
include "bitri.mm"

theorem dfsymrel2
  let cR: class R


  assert |- ( SymRel R <-> ( `' R C_ R /\ Rel R ) )

  proof
    cR
    wsymrel
    cR
    cR
    cdm
    cR
    crn
    cxp
    cin
    #
    ccnv
    #
    @0
    wss
    #
    cR
    wrel
    #
    wa
    cR
    ccnv
    #
    cR
    wss
    #
    @3
    wa
    cR
    df-symrel
    @3
    @2
    @5
    @3
    @1
    @4
    @0
    cR
    @3
    @0
    cR
    @3
    @0
    cR
    wceq
    cR
    dfrel6
    biimpi
    #
    cnveqd
    @6
    sseq12d
    pm5.32ri
    bitri
end
