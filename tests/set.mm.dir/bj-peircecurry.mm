include "wi.mm"
include "wo.mm"
include "orc.mm"
include "olc.mm"
include "peirce.mm"
include "peirceroll.mm"
include "ax-mp.mm"
include "mpsyl.mm"

theorem bj-peircecurry
  let wph: wff ph
  let wps: wff ps


  assert |- ( ph \/ ( ph -> ps ) )

  proof
    wph
    wph
    wph
    wps
    wi
    #
    wo
    #
    wi
    #
    @1
    wph
    @0
    orc
    @0
    @1
    wi
    #
    @2
    @1
    wi
    #
    @0
    wph
    olc
    @1
    wph
    wi
    #
    @1
    wi
    @1
    wi
    @3
    @5
    wph
    wi
    #
    @4
    @1
    wph
    peirce
    @0
    wph
    wi
    wph
    wi
    @3
    @6
    wi
    wph
    wps
    peirce
    wph
    wps
    @1
    peirceroll
    ax-mp
    @1
    wph
    wph
    peirceroll
    mpsyl
    ax-mp
    ax-mp
end
