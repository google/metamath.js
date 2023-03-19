include "wi.mm"
include "ax-frege2.mm"
include "rp-frege24.mm"
include "ax-mp.mm"

theorem rp-7frege
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th


  assert |- ( ( ph -> ( ps -> ch ) ) -> ( th -> ( ( ph -> ps ) -> ( ph -> ch ) ) ) )

  proof
    wph
    wps
    wch
    wi
    wi
    #
    wph
    wps
    wi
    wph
    wch
    wi
    wi
    #
    wi
    @0
    wth
    @1
    wi
    wi
    wph
    wps
    wch
    ax-frege2
    @0
    @1
    wth
    rp-frege24
    ax-mp
end
