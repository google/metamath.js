include "wi.mm"
include "wn.mm"
include "meredith.mm"
include "merlem7.mm"
include "ax-mp.mm"

theorem merlem8
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wph: wff ph


  assert |- ( ( ( ps -> ch ) -> th ) -> ( ( ( ch -> ta ) -> ( -. th -> -. ps ) ) -> th ) )

  proof
    wph
    wph
    wi
    #
    wph
    wn
    #
    @1
    wi
    wi
    wph
    wi
    wph
    wi
    @0
    @0
    wi
    wi
    #
    wps
    wch
    wi
    wth
    wi
    wch
    wta
    wi
    wth
    wn
    wps
    wn
    wi
    wi
    wth
    wi
    wi
    wph
    wph
    wph
    wph
    wph
    meredith
    @2
    wps
    wch
    wth
    wta
    merlem7
    ax-mp
end
