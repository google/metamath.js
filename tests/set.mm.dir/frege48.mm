include "wn.mm"
include "wi.mm"
include "frege47.mm"
include "frege23.mm"
include "ax-mp.mm"

theorem frege48
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th


  assert |- ( ( ph -> ( -. ps -> ch ) ) -> ( ( ch -> th ) -> ( ( ps -> th ) -> ( ph -> th ) ) ) )

  proof
    wps
    wn
    wch
    wi
    #
    wch
    wth
    wi
    #
    wps
    wth
    wi
    #
    wth
    wi
    wi
    wi
    wph
    @0
    wi
    @1
    @2
    wph
    wth
    wi
    wi
    wi
    wi
    wps
    wch
    wth
    frege47
    @0
    @1
    @2
    wth
    wph
    frege23
    ax-mp
end
