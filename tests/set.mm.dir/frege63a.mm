include "wif.mm"
include "wi.mm"
include "wa.mm"
include "frege62a.mm"
include "frege24.mm"
include "ax-mp.mm"

theorem frege63a
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et


  assert |- ( if- ( ph , ps , th ) -> ( et -> ( ( ( ps -> ch ) /\ ( th -> ta ) ) -> if- ( ph , ch , ta ) ) ) )

  proof
    wph
    wps
    wth
    wif
    #
    wps
    wch
    wi
    wth
    wta
    wi
    wa
    wph
    wch
    wta
    wif
    wi
    #
    wi
    @0
    wet
    @1
    wi
    wi
    wph
    wps
    wch
    wth
    wta
    frege62a
    @0
    @1
    wet
    frege24
    ax-mp
end
