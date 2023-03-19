include "wrefrel.mm"
include "cid.mm"
include "cdm.mm"
include "crn.mm"
include "cxp.mm"
include "cin.mm"
include "wss.mm"
include "wrel.mm"
include "wa.mm"
include "df-refrel.mm"
include "wceq.mm"
include "dfrel6.mm"
include "biimpi.mm"
include "sseq2d.mm"
include "pm5.32ri.mm"
include "bitri.mm"

theorem dfrefrel2
  let cR: class R


  assert |- ( RefRel R <-> ( ( _I i^i ( dom R X. ran R ) ) C_ R /\ Rel R ) )

  proof
    cR
    wrefrel
    cid
    cR
    cdm
    cR
    crn
    cxp
    #
    cin
    #
    cR
    @0
    cin
    #
    wss
    #
    cR
    wrel
    #
    wa
    @1
    cR
    wss
    #
    @4
    wa
    cR
    df-refrel
    @4
    @3
    @5
    @4
    @2
    cR
    @1
    @4
    @2
    cR
    wceq
    cR
    dfrel6
    biimpi
    sseq2d
    pm5.32ri
    bitri
end
