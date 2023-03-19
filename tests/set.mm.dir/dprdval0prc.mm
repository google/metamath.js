include "cdm.mm"
include "cvv.mm"
include "wnel.mm"
include "wcel.mm"
include "wn.mm"
include "cdprd.mm"
include "co.mm"
include "c0.mm"
include "wceq.mm"
include "df-nel.mm"
include "dmexg.mm"
include "con3i.mm"
include "sylbi.mm"
include "reldmdprd.mm"
include "ovprc2.mm"
include "syl.mm"

theorem dprdval0prc
  let cS: class S
  let cG: class G


  assert |- ( dom S e/ _V -> ( G DProd S ) = (/) )

  proof
    cS
    cdm
    #
    cvv
    wnel
    #
    cS
    cvv
    wcel
    #
    wn
    #
    cG
    cS
    cdprd
    co
    c0
    wceq
    @1
    @0
    cvv
    wcel
    #
    wn
    @3
    @0
    cvv
    df-nel
    @2
    @4
    cS
    cvv
    dmexg
    con3i
    sylbi
    cG
    cS
    cdprd
    reldmdprd
    ovprc2
    syl
end
