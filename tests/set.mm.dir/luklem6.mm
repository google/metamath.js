include "wi.mm"
include "luk-1.mm"
include "wn.mm"
include "luklem5.mm"
include "luklem2.mm"
include "luklem4.mm"
include "luklem1.mm"
include "ax-mp.mm"

theorem luklem6
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( ph -> ( ph -> ps ) ) -> ( ph -> ps ) )

  proof
    wph
    wph
    wps
    wi
    #
    wi
    @0
    wps
    wi
    #
    @0
    wi
    #
    @0
    wph
    @0
    wps
    luk-1
    @0
    wn
    #
    @0
    wi
    #
    @0
    wi
    @2
    @0
    wi
    #
    wi
    #
    @5
    @2
    @4
    wi
    #
    @6
    @3
    @1
    wi
    @7
    @3
    wps
    wn
    #
    @3
    wi
    #
    @1
    @3
    @8
    luklem5
    @9
    @8
    wps
    wi
    wps
    wi
    @1
    wi
    @1
    @8
    @0
    wps
    wps
    luklem2
    wps
    @1
    luklem4
    luklem1
    luklem1
    @3
    @1
    @0
    luk-1
    ax-mp
    @2
    @4
    @0
    luk-1
    ax-mp
    @0
    @5
    luklem4
    ax-mp
    luklem1
end
