include "wi.mm"
include "wn.mm"
include "frege50.mm"
include "frege18.mm"
include "ax-mp.mm"

theorem frege51
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th


  assert |- ( ( ph -> ( ps -> ch ) ) -> ( ( th -> ch ) -> ( ph -> ( ( -. ps -> th ) -> ch ) ) ) )

  proof
    wps
    wch
    wi
    #
    wth
    wch
    wi
    #
    wps
    wn
    wth
    wi
    wch
    wi
    #
    wi
    wi
    wph
    @0
    wi
    @1
    wph
    @2
    wi
    wi
    wi
    wps
    wch
    wth
    frege50
    @0
    @1
    @2
    wph
    frege18
    ax-mp
end
