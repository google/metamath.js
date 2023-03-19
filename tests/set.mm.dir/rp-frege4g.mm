include "wi.mm"
include "rp-frege3g.mm"
include "ax-frege2.mm"
include "ax-mp.mm"

theorem rp-frege4g
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th


  assert |- ( ( ph -> ( ps -> ( ch -> th ) ) ) -> ( ph -> ( ( ps -> ch ) -> ( ps -> th ) ) ) )

  proof
    wph
    wps
    wch
    wth
    wi
    wi
    #
    wps
    wch
    wi
    wps
    wth
    wi
    wi
    #
    wi
    wi
    wph
    @0
    wi
    wph
    @1
    wi
    wi
    wph
    wps
    wch
    wth
    rp-frege3g
    wph
    @0
    @1
    ax-frege2
    ax-mp
end
