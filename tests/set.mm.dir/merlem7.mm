include "wi.mm"
include "wn.mm"
include "merlem4.mm"
include "merlem6.mm"
include "meredith.mm"
include "ax-mp.mm"

theorem merlem7
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta


  assert |- ( ph -> ( ( ( ps -> ch ) -> th ) -> ( ( ( ch -> ta ) -> ( -. th -> -. ps ) ) -> th ) ) )

  proof
    wps
    wch
    wi
    #
    @0
    wth
    wi
    #
    wch
    wta
    wi
    wth
    wn
    wps
    wn
    wi
    wi
    #
    wth
    wi
    #
    wi
    #
    wi
    #
    wph
    @4
    wi
    #
    wth
    @2
    @0
    merlem4
    @4
    wph
    wn
    #
    wi
    wch
    wn
    #
    @7
    wi
    wi
    #
    wch
    wi
    @0
    wi
    #
    @5
    @6
    wi
    @3
    @9
    wi
    @10
    @7
    @1
    @3
    @8
    merlem6
    wch
    wta
    wth
    wps
    @9
    meredith
    ax-mp
    @4
    @7
    wch
    wph
    @0
    meredith
    ax-mp
    ax-mp
end
