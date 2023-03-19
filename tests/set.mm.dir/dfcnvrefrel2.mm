include "wcnvrefrel.mm"
include "cdm.mm"
include "crn.mm"
include "cxp.mm"
include "cin.mm"
include "cid.mm"
include "wss.mm"
include "wrel.mm"
include "wa.mm"
include "df-cnvrefrel.mm"
include "wceq.mm"
include "dfrel6.mm"
include "biimpi.mm"
include "sseq1d.mm"
include "pm5.32ri.mm"
include "bitri.mm"

theorem dfcnvrefrel2
  let cR: class R


  assert |- ( CnvRefRel R <-> ( R C_ ( _I i^i ( dom R X. ran R ) ) /\ Rel R ) )

  proof
    cR
    wcnvrefrel
    cR
    cR
    cdm
    cR
    crn
    cxp
    #
    cin
    #
    cid
    @0
    cin
    #
    wss
    #
    cR
    wrel
    #
    wa
    cR
    @2
    wss
    #
    @4
    wa
    cR
    df-cnvrefrel
    @4
    @3
    @5
    @4
    @1
    cR
    @2
    @4
    @1
    cR
    wceq
    cR
    dfrel6
    biimpi
    sseq1d
    pm5.32ri
    bitri
end
