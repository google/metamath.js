include "c1.mm"
include "codd.mm"
include "wcel.mm"
include "ceven.mm"
include "wnel.mm"
include "1oddALTV.mm"
include "wn.mm"
include "cz.mm"
include "wb.mm"
include "1z.mm"
include "zeo2ALTV.mm"
include "ax-mp.mm"
include "con2bii.mm"
include "df-nel.mm"
include "bitr4i.mm"
include "mpbi.mm"

theorem 1nevenALTV
  let vk: setvar k
  let vx: setvar x


  assert |- 1 e/ Even

  proof
    c1
    codd
    wcel
    #
    c1
    ceven
    wnel
    #
    1oddALTV
    @0
    c1
    ceven
    wcel
    #
    wn
    @1
    @2
    @0
    c1
    cz
    wcel
    @2
    @0
    wn
    wb
    1z
    c1
    zeo2ALTV
    ax-mp
    con2bii
    c1
    ceven
    df-nel
    bitr4i
    mpbi
end
