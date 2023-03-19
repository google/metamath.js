include "wi.mm"
include "wa.mm"
include "wif.mm"
include "wn.mm"
include "frege58acor.mm"
include "frege30.mm"
include "ax-mp.mm"

theorem frege59a
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta


  assert |- ( if- ( ph , ps , th ) -> ( -. if- ( ph , ch , ta ) -> -. ( ( ps -> ch ) /\ ( th -> ta ) ) ) )

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
    @2
    wn
    @0
    wn
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
    frege30
    ax-mp
end
