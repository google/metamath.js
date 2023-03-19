include "vd01.mm"
include "e112.mm"

theorem e102
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume e102.1: |- (. ph ->. ps ).
  assume e102.2: |- ch
  assume e102.3: |- (. ph ,. th ->. ta ).
  assume e102.4: |- ( ps -> ( ch -> ( ta -> et ) ) )


  assert |- (. ph ,. th ->. et ).

  proof
    wph
    wps
    wch
    wth
    wta
    wet
    e102.1
    wch
    wph
    e102.2
    vd01
    e102.3
    e102.4
    e112
end
