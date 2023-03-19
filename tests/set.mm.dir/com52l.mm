include "com5l.mm"

theorem com52l
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume com5.1: |- ( ph -> ( ps -> ( ch -> ( th -> ( ta -> et ) ) ) ) )


  assert |- ( ch -> ( th -> ( ta -> ( ph -> ( ps -> et ) ) ) ) )

  proof
    wps
    wch
    wth
    wta
    wph
    wet
    wph
    wps
    wch
    wth
    wta
    wet
    com5.1
    com5l
    com5l
end
