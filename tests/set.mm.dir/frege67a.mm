include "wa.mm"
include "wif.mm"
include "wi.mm"
include "wb.mm"
include "ax-frege58a.mm"
include "frege7.mm"
include "ax-mp.mm"

theorem frege67a
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th


  assert |- ( ( ( ( ps /\ ch ) <-> th ) -> ( th -> ( ps /\ ch ) ) ) -> ( ( ( ps /\ ch ) <-> th ) -> ( th -> if- ( ph , ps , ch ) ) ) )

  proof
    wps
    wch
    wa
    #
    wph
    wps
    wch
    wif
    #
    wi
    @0
    wth
    wb
    #
    wth
    @0
    wi
    wi
    @2
    wth
    @1
    wi
    wi
    wi
    wph
    wps
    wch
    ax-frege58a
    @0
    @1
    @2
    wth
    frege7
    ax-mp
end
