include "com52l.mm"

theorem com5r
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume com5.1: |- ( ph -> ( ps -> ( ch -> ( th -> ( ta -> et ) ) ) ) )


  assert |- ( ta -> ( ph -> ( ps -> ( ch -> ( th -> et ) ) ) ) )

  proof
    wch
    wth
    wta
    wph
    wps
    wet
    wph
    wps
    wch
    wth
    wta
    wet
    com5.1
    com52l
    com52l
end
