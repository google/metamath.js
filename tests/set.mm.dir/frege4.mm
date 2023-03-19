include "wi.mm"
include "frege3.mm"
include "ax-frege2.mm"
include "ax-mp.mm"

theorem frege4
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ( ph -> ps ) -> ( ch -> ( ph -> ps ) ) ) -> ( ( ph -> ps ) -> ( ( ch -> ph ) -> ( ch -> ps ) ) ) )

  proof
    wph
    wps
    wi
    #
    wch
    @0
    wi
    #
    wch
    wph
    wi
    wch
    wps
    wi
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
    frege3
    @0
    @1
    @2
    ax-frege2
    ax-mp
end
