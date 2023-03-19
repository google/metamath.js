include "cc0.mm"
include "codd.mm"
include "wnel.mm"
include "ceven.mm"
include "wcel.mm"
include "0evenALTV.mm"
include "wn.mm"
include "df-nel.mm"
include "cz.mm"
include "wb.mm"
include "0z.mm"
include "zeo2ALTV.mm"
include "bicomd.mm"
include "ax-mp.mm"
include "bitri.mm"
include "mpbir.mm"

theorem 0noddALTV
  let vk: setvar k
  let vx: setvar x


  assert |- 0 e/ Odd

  proof
    cc0
    codd
    wnel
    #
    cc0
    ceven
    wcel
    #
    0evenALTV
    @0
    cc0
    codd
    wcel
    wn
    #
    @1
    cc0
    codd
    df-nel
    cc0
    cz
    wcel
    #
    @2
    @1
    wb
    0z
    @3
    @1
    @2
    cc0
    zeo2ALTV
    bicomd
    ax-mp
    bitri
    mpbir
end
