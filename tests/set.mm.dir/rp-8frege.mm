include "wi.mm"
include "rp-6frege.mm"
include "ax-frege2.mm"
include "ax-mp.mm"

theorem rp-8frege
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th


  assert |- ( ( ph -> ( ps -> ( ( ch -> ps ) -> th ) ) ) -> ( ph -> ( ps -> th ) ) )

  proof
    wph
    wps
    wch
    wps
    wi
    wth
    wi
    wi
    #
    wps
    wth
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
    rp-6frege
    wph
    @0
    @1
    ax-frege2
    ax-mp
end
