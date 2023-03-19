include "cdm.mm"
include "cvv.mm"
include "wnel.mm"
include "wcel.mm"
include "cdprd.mm"
include "wbr.mm"
include "wn.mm"
include "df-nel.mm"
include "dmexg.mm"
include "con3i.mm"
include "sylbi.mm"
include "reldmdprd.mm"
include "brrelex2i.mm"
include "nsyl.mm"

theorem dprddomprc
  let cS: class S
  let cG: class G


  assert |- ( dom S e/ _V -> -. G dom DProd S )

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
    cG
    cS
    cdprd
    cdm
    #
    wbr
    @1
    @0
    cvv
    wcel
    #
    wn
    @2
    wn
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
    @3
    reldmdprd
    brrelex2i
    nsyl
end
