include "wif.mm"
include "wi.mm"
include "wa.mm"
include "frege62a.mm"
include "frege18.mm"
include "ax-mp.mm"

theorem frege64a
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  let wze: wff ze
  let wsi: wff si


  assert |- ( ( if- ( ph , ps , ta ) -> if- ( si , ch , et ) ) -> ( ( ( ch -> th ) /\ ( et -> ze ) ) -> ( if- ( ph , ps , ta ) -> if- ( si , th , ze ) ) ) )

  proof
    wsi
    wch
    wet
    wif
    #
    wch
    wth
    wi
    wet
    wze
    wi
    wa
    #
    wsi
    wth
    wze
    wif
    #
    wi
    wi
    wph
    wps
    wta
    wif
    #
    @0
    wi
    @1
    @3
    @2
    wi
    wi
    wi
    wsi
    wch
    wth
    wet
    wze
    frege62a
    @0
    @1
    @2
    @3
    frege18
    ax-mp
end
