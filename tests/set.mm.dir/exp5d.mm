include "wi.mm"
include "wa.mm"
include "expd.mm"
include "exp31.mm"

theorem exp5d
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume exp5d.1: |- ( ( ( ph /\ ps ) /\ ch ) -> ( ( th /\ ta ) -> et ) )


  assert |- ( ph -> ( ps -> ( ch -> ( th -> ( ta -> et ) ) ) ) )

  proof
    wph
    wps
    wch
    wth
    wta
    wet
    wi
    wi
    wph
    wps
    wa
    wch
    wa
    wth
    wta
    wet
    exp5d.1
    expd
    exp31
end
