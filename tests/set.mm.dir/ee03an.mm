include "ex.mm"
include "ee03.mm"

theorem ee03an
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume ee03an.1: |- ph
  assume ee03an.2: |- ( ps -> ( ch -> ( th -> ta ) ) )
  assume ee03an.3: |- ( ( ph /\ ta ) -> et )


  assert |- ( ps -> ( ch -> ( th -> et ) ) )

  proof
    wph
    wps
    wch
    wth
    wta
    wet
    ee03an.1
    ee03an.2
    wph
    wta
    wet
    ee03an.3
    ex
    ee03
end
