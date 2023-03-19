include "ex.mm"
include "ee13.mm"

theorem ee13an
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume ee13an.1: |- ( ph -> ps )
  assume ee13an.2: |- ( ph -> ( ch -> ( th -> ta ) ) )
  assume ee13an.3: |- ( ( ps /\ ta ) -> et )


  assert |- ( ph -> ( ch -> ( th -> et ) ) )

  proof
    wph
    wps
    wch
    wth
    wta
    wet
    ee13an.1
    ee13an.2
    wps
    wta
    wet
    ee13an.3
    ex
    ee13
end
