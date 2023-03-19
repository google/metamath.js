include "wi.mm"
include "wa.mm"
include "wif.mm"
include "ax-frege58a.mm"
include "ifpimim.mm"
include "syl.mm"

theorem frege58acor
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta


  assert |- ( ( ( ps -> ch ) /\ ( th -> ta ) ) -> ( if- ( ph , ps , th ) -> if- ( ph , ch , ta ) ) )

  proof
    wps
    wch
    wi
    #
    wth
    wta
    wi
    #
    wa
    wph
    @0
    @1
    wif
    wph
    wps
    wth
    wif
    wph
    wch
    wta
    wif
    wi
    wph
    @0
    @1
    ax-frege58a
    wph
    wps
    wch
    wth
    wta
    ifpimim
    syl
end
