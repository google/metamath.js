include "wi.mm"
include "rp-4frege.mm"
include "ax-frege1.mm"
include "ax-mp.mm"

theorem rp-6frege
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th


  assert |- ( ph -> ( ( ps -> ( ( ch -> ps ) -> th ) ) -> ( ps -> th ) ) )

  proof
    wps
    wch
    wps
    wi
    wth
    wi
    wi
    wps
    wth
    wi
    wi
    #
    wph
    @0
    wi
    wps
    wch
    wth
    rp-4frege
    @0
    wph
    ax-frege1
    ax-mp
end
