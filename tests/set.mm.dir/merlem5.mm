include "wi.mm"
include "wn.mm"
include "meredith.mm"
include "merlem1.mm"
include "merlem4.mm"
include "ax-mp.mm"

theorem merlem5
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( ph -> ps ) -> ( -. -. ph -> ps ) )

  proof
    wps
    wps
    wi
    #
    wps
    wn
    #
    @1
    wi
    wi
    wps
    wi
    wps
    wi
    @0
    @0
    wi
    wi
    #
    wph
    wps
    wi
    #
    wph
    wn
    #
    wn
    #
    wps
    wi
    wi
    #
    wps
    wps
    wps
    wps
    wps
    meredith
    @0
    @1
    @5
    wn
    wi
    wi
    wps
    wi
    #
    wph
    wi
    #
    @6
    wi
    #
    @2
    @6
    wi
    #
    wps
    wps
    wps
    @5
    wph
    meredith
    @6
    @2
    wn
    #
    wi
    @4
    @11
    wi
    wi
    #
    wph
    wi
    @8
    wi
    #
    @9
    @10
    wi
    @12
    @13
    @4
    wps
    @3
    @11
    merlem1
    wph
    @7
    @12
    merlem4
    ax-mp
    @6
    @11
    wph
    @2
    @8
    meredith
    ax-mp
    ax-mp
    ax-mp
end
