include "wi.mm"
include "a1d.mm"
include "ee33an.mm"

theorem ee31an
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume ee31an.1: |- ( ph -> ( ps -> ( ch -> th ) ) )
  assume ee31an.2: |- ( ph -> ta )
  assume ee31an.3: |- ( ( th /\ ta ) -> et )


  assert |- ( ph -> ( ps -> ( ch -> et ) ) )

  proof
    wph
    wps
    wch
    wth
    wta
    wet
    ee31an.1
    wph
    wch
    wta
    wi
    wps
    wph
    wta
    wch
    ee31an.2
    a1d
    a1d
    ee31an.3
    ee33an
end
