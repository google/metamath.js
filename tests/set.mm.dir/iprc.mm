include "cid.mm"
include "cvv.mm"
include "wcel.mm"
include "cdm.mm"
include "vprc.mm"
include "dmi.mm"
include "eleq1i.mm"
include "mtbir.mm"
include "dmexg.mm"
include "mto.mm"

theorem iprc



  assert |- -. _I e. _V

  proof
    cid
    cvv
    wcel
    cid
    cdm
    #
    cvv
    wcel
    #
    @1
    cvv
    cvv
    wcel
    vprc
    @0
    cvv
    cvv
    dmi
    eleq1i
    mtbir
    cid
    cvv
    dmexg
    mto
end
