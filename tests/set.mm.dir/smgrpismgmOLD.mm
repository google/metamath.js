include "cmagm.mm"
include "wcel.mm"
include "cass.mm"
include "cin.mm"
include "csem.mm"
include "elin.mm"
include "simplbi.mm"
include "df-sgrOLD.mm"
include "eleq2s.mm"

theorem smgrpismgmOLD
  let cG: class G


  assert |- ( G e. SemiGrp -> G e. Magma )

  proof
    cG
    cmagm
    wcel
    #
    cG
    cmagm
    cass
    cin
    #
    csem
    cG
    @1
    wcel
    @0
    cG
    cass
    wcel
    cG
    cmagm
    cass
    elin
    simplbi
    df-sgrOLD
    eleq2s
end
