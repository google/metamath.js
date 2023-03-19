include "cz.mm"
include "wcel.mm"
include "ceven.mm"
include "codd.mm"
include "wn.mm"
include "evennodd.mm"
include "wo.mm"
include "wi.mm"
include "zeoALTV.mm"
include "ax-1.mm"
include "pm2.24.mm"
include "jaoi.mm"
include "syl.mm"
include "impbid2.mm"

theorem zeo2ALTV
  let cZ: class Z
  let vk: setvar k
  let vx: setvar x


  assert |- ( Z e. ZZ -> ( Z e. Even <-> -. Z e. Odd ) )

  proof
    cZ
    cz
    wcel
    #
    cZ
    ceven
    wcel
    #
    cZ
    codd
    wcel
    #
    wn
    #
    cZ
    evennodd
    @0
    @1
    @2
    wo
    @3
    @1
    wi
    #
    cZ
    zeoALTV
    @1
    @4
    @2
    @1
    @3
    ax-1
    @2
    @1
    pm2.24
    jaoi
    syl
    impbid2
end
