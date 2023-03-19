include "com52l.mm"
include "com5l.mm"

theorem com52r
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume com5.1: |- ( ph -> ( ps -> ( ch -> ( th -> ( ta -> et ) ) ) ) )


  assert |- ( th -> ( ta -> ( ph -> ( ps -> ( ch -> et ) ) ) ) )

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
    com5l
end
