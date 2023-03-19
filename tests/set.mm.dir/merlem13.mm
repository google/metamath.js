include "wi.mm"
include "wn.mm"
include "merlem12.mm"
include "merlem5.mm"
include "ax-mp.mm"
include "merlem6.mm"
include "meredith.mm"
include "merlem11.mm"

theorem merlem13
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th


  assert |- ( ( ph -> ps ) -> ( ( ( th -> ( -. -. ch -> ch ) ) -> -. -. ph ) -> ps ) )

  proof
    wps
    wps
    wi
    #
    wph
    wn
    #
    wth
    wch
    wn
    wn
    wch
    wi
    wi
    #
    @1
    wn
    #
    wi
    #
    wn
    #
    wi
    #
    wi
    wph
    wi
    #
    wph
    wi
    #
    wph
    wps
    wi
    @4
    wps
    wi
    wi
    @7
    @8
    wi
    #
    @8
    @6
    @9
    @2
    @5
    wi
    #
    @5
    wi
    #
    @6
    @5
    wch
    wth
    merlem12
    @5
    wps
    wi
    #
    @5
    wn
    @3
    wi
    #
    wi
    @5
    wi
    @10
    wi
    #
    @11
    @6
    wi
    @13
    @14
    @4
    @3
    wi
    @13
    @3
    wch
    wth
    merlem12
    @4
    @3
    merlem5
    ax-mp
    @5
    @12
    @13
    @2
    merlem6
    ax-mp
    @5
    wps
    @5
    @1
    @10
    meredith
    ax-mp
    ax-mp
    wph
    @0
    @6
    @7
    merlem6
    ax-mp
    @7
    wph
    merlem11
    ax-mp
    wps
    wps
    wph
    @4
    wph
    meredith
    ax-mp
end
