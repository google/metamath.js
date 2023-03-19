include "wa.mm"
include "wb.mm"
include "wi.mm"
include "wif.mm"
include "frege57aid.mm"
include "frege67a.mm"
include "ax-mp.mm"

theorem frege68a
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th


  assert |- ( ( ( ps /\ ch ) <-> th ) -> ( th -> if- ( ph , ps , ch ) ) )

  proof
    wps
    wch
    wa
    #
    wth
    wb
    #
    wth
    @0
    wi
    wi
    @1
    wth
    wph
    wps
    wch
    wif
    wi
    wi
    @0
    wth
    frege57aid
    wph
    wps
    wch
    wth
    frege67a
    ax-mp
end
