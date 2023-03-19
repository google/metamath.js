include "cmagm.mm"
include "cexid.mm"
include "cin.mm"
include "wcel.mm"
include "cdm.mm"
include "cxp.mm"
include "wfo.mm"
include "crn.mm"
include "wceq.mm"
include "eqid.mm"
include "opidonOLD.mm"
include "forn.mm"
include "syl.mm"

theorem rngopidOLD
  let cG: class G


  assert |- ( G e. ( Magma i^i ExId ) -> ran G = dom dom G )

  proof
    cG
    cmagm
    cexid
    cin
    wcel
    cG
    cdm
    cdm
    #
    @0
    cxp
    #
    @0
    cG
    wfo
    cG
    crn
    @0
    wceq
    cG
    @0
    @0
    eqid
    opidonOLD
    @1
    @0
    cG
    forn
    syl
end
