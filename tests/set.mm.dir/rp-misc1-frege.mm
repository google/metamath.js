include "wi.mm"
include "ax-frege2.mm"
include "ax-mp.mm"

theorem rp-misc1-frege
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ( ph -> ( ps -> ch ) ) -> ( ph -> ps ) ) -> ( ( ph -> ( ps -> ch ) ) -> ( ph -> ch ) ) )

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
    #
    wph
    wch
    wi
    #
    wi
    wi
    @0
    @1
    wi
    @0
    @2
    wi
    wi
    wph
    wps
    wch
    ax-frege2
    @0
    @1
    @2
    ax-frege2
    ax-mp
end
