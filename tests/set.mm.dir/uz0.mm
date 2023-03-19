include "cz.mm"
include "wcel.mm"
include "wn.mm"
include "cuz.mm"
include "cdm.mm"
include "cfv.mm"
include "c0.mm"
include "wceq.mm"
include "dmuz.mm"
include "eqcomi.mm"
include "eleq2i.mm"
include "notbii.mm"
include "biimpi.mm"
include "ndmfv.mm"
include "syl.mm"

theorem uz0
  let cM: class M


  assert |- ( -. M e. ZZ -> ( ZZ>= ` M ) = (/) )

  proof
    cM
    cz
    wcel
    #
    wn
    #
    cM
    cuz
    cdm
    #
    wcel
    #
    wn
    #
    cM
    cuz
    cfv
    c0
    wceq
    @1
    @4
    @0
    @3
    cz
    @2
    cM
    @2
    cz
    dmuz
    eqcomi
    eleq2i
    notbii
    biimpi
    cM
    cuz
    ndmfv
    syl
end
