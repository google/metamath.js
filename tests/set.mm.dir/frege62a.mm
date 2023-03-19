include "wi.mm"
include "wa.mm"
include "wif.mm"
include "frege58acor.mm"
include "ax-frege8.mm"
include "ax-mp.mm"

theorem frege62a
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta


  assert |- ( if- ( ph , ps , th ) -> ( ( ( ps -> ch ) /\ ( th -> ta ) ) -> if- ( ph , ch , ta ) ) )

  proof
    wps
    wch
    wi
    wth
    wta
    wi
    wa
    #
    wph
    wps
    wth
    wif
    #
    wph
    wch
    wta
    wif
    #
    wi
    wi
    @1
    @0
    @2
    wi
    wi
    wph
    wps
    wch
    wth
    wta
    frege58acor
    @0
    @1
    @2
    ax-frege8
    ax-mp
end
