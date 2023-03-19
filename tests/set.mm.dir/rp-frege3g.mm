include "wi.mm"
include "ax-frege2.mm"
include "ax-frege1.mm"
include "ax-mp.mm"

theorem rp-frege3g
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th


  assert |- ( ph -> ( ( ps -> ( ch -> th ) ) -> ( ( ps -> ch ) -> ( ps -> th ) ) ) )

  proof
    wps
    wch
    wth
    wi
    wi
    wps
    wch
    wi
    wps
    wth
    wi
    wi
    wi
    #
    wph
    @0
    wi
    wps
    wch
    wth
    ax-frege2
    @0
    wph
    ax-frege1
    ax-mp
end
