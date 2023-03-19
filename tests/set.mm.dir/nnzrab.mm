include "cn.mm"
include "cv.mm"
include "cz.mm"
include "wcel.mm"
include "c1.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "cab.mm"
include "crab.mm"
include "elnnz1.mm"
include "abbi2i.mm"
include "df-rab.mm"
include "eqtr4i.mm"

theorem nnzrab
  let vx: setvar x


  assert |- NN = { x e. ZZ | 1 <_ x }

  proof
    cn
    vx
    cv
    #
    cz
    wcel
    c1
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
    cn
    @0
    elnnz1
    abbi2i
    @1
    vx
    cz
    df-rab
    eqtr4i
end
