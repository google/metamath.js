include "wi.mm"
include "wa.mm"
include "exp4c.mm"
include "ex.mm"

theorem exp5g
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume exp5g.1: |- ( ( ph /\ ps ) -> ( ( ( ch /\ th ) /\ ta ) -> et ) )


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
    wi
    wph
    wps
    wa
    wch
    wth
    wta
    wet
    exp5g.1
    exp4c
    ex
end
