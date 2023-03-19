include "cn0.mm"
include "cv.mm"
include "cz.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "cab.mm"
include "crab.mm"
include "elnn0z.mm"
include "abbi2i.mm"
include "df-rab.mm"
include "eqtr4i.mm"

theorem nn0zrab
  let vx: setvar x


  assert |- NN0 = { x e. ZZ | 0 <_ x }

  proof
    cn0
    vx
    cv
    #
    cz
    wcel
    cc0
    @0
    cle
    wbr
    #
    wa
    #
    vx
    cab
    @1
    vx
    cz
    crab
    @2
    vx
    cn0
    @0
    elnn0z
    abbi2i
    @1
    vx
    cz
    df-rab
    eqtr4i
end
