include "c2.mm"
include "codd.mm"
include "wnel.mm"
include "ceven.mm"
include "wcel.mm"
include "2evenALTV.mm"
include "wn.mm"
include "df-nel.mm"
include "cz.mm"
include "wb.mm"
include "2z.mm"
include "zeo2ALTV.mm"
include "bicomd.mm"
include "ax-mp.mm"
include "bitri.mm"
include "mpbir.mm"

theorem 2noddALTV
  let vk: setvar k
  let vx: setvar x


  assert |- 2 e/ Odd

  proof
    c2
    codd
    wnel
    #
    c2
    ceven
    wcel
    #
    2evenALTV
    @0
    c2
    codd
    wcel
    wn
    #
    @1
    c2
    codd
    df-nel
    c2
    cz
    wcel
    #
    @2
    @1
    wb
    2z
    @3
    @1
    @2
    c2
    zeo2ALTV
    bicomd
    ax-mp
    bitri
    mpbir
end
