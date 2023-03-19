include "wa.mm"
include "wif.mm"
include "wi.mm"
include "ax-frege58a.mm"
include "frege9.mm"
include "ax-mp.mm"

theorem frege61a
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th


  assert |- ( ( if- ( ph , ps , ch ) -> th ) -> ( ( ps /\ ch ) -> th ) )

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
    @1
    wth
    wi
    @0
    wth
    wi
    wi
    wph
    wps
    wch
    ax-frege58a
    @0
    @1
    wth
    frege9
    ax-mp
end
