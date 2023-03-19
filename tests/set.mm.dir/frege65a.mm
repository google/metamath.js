include "wi.mm"
include "wif.mm"
include "wa.mm"
include "ifpimim.mm"
include "frege64a.mm"
include "syl.mm"
include "frege61a.mm"
include "ax-mp.mm"

theorem frege65a
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  let wze: wff ze


  assert |- ( ( ( ps -> ch ) /\ ( ta -> et ) ) -> ( ( ( ch -> th ) /\ ( et -> ze ) ) -> ( if- ( ph , ps , ta ) -> if- ( ph , th , ze ) ) ) )

  proof
    wph
    wps
    wch
    wi
    #
    wta
    wet
    wi
    #
    wif
    #
    wch
    wth
    wi
    wet
    wze
    wi
    wa
    wph
    wps
    wta
    wif
    #
    wph
    wth
    wze
    wif
    wi
    wi
    #
    wi
    @0
    @1
    wa
    @4
    wi
    @2
    @3
    wph
    wch
    wet
    wif
    wi
    @4
    wph
    wps
    wch
    wta
    wet
    ifpimim
    wph
    wps
    wch
    wth
    wta
    wet
    wze
    wph
    frege64a
    syl
    wph
    @0
    @1
    @4
    frege61a
    ax-mp
end
