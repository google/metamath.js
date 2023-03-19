include "wi.mm"
include "wa.mm"
include "wif.mm"
include "frege58acor.mm"
include "ifpimim.mm"
include "syl6.mm"
include "frege12.mm"
include "ax-mp.mm"

theorem frege60a
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  let wze: wff ze


  assert |- ( ( ( ps -> ( ch -> th ) ) /\ ( ta -> ( et -> ze ) ) ) -> ( if- ( ph , ch , et ) -> ( if- ( ph , ps , ta ) -> if- ( ph , th , ze ) ) ) )

  proof
    wps
    wch
    wth
    wi
    #
    wi
    wta
    wet
    wze
    wi
    #
    wi
    wa
    #
    wph
    wps
    wta
    wif
    #
    wph
    wch
    wet
    wif
    #
    wph
    wth
    wze
    wif
    #
    wi
    #
    wi
    wi
    @2
    @4
    @3
    @5
    wi
    wi
    wi
    @2
    @3
    wph
    @0
    @1
    wif
    @6
    wph
    wps
    @0
    wta
    @1
    frege58acor
    wph
    wch
    wth
    wet
    wze
    ifpimim
    syl6
    @2
    @3
    @4
    @5
    frege12
    ax-mp
end
