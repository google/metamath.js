include "wi.mm"
include "wa.mm"
include "wif.mm"
include "frege65a.mm"
include "ax-frege8.mm"
include "ax-mp.mm"

theorem frege66a
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  let wze: wff ze


  assert |- ( ( ( ch -> th ) /\ ( et -> ze ) ) -> ( ( ( ps -> ch ) /\ ( ta -> et ) ) -> ( if- ( ph , ps , ta ) -> if- ( ph , th , ze ) ) ) )

  proof
    wps
    wch
    wi
    wta
    wet
    wi
    wa
    #
    wch
    wth
    wi
    wet
    wze
    wi
    wa
    #
    wph
    wps
    wta
    wif
    wph
    wth
    wze
    wif
    wi
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
    wet
    wze
    frege65a
    @0
    @1
    @2
    ax-frege8
    ax-mp
end
