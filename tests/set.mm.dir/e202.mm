include "vd02.mm"
include "e222.mm"

theorem e202
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume e202.1: |- (. ph ,. ps ->. ch ).
  assume e202.2: |- th
  assume e202.3: |- (. ph ,. ps ->. ta ).
  assume e202.4: |- ( ch -> ( th -> ( ta -> et ) ) )


  assert |- (. ph ,. ps ->. et ).

  proof
    wph
    wps
    wch
    wth
    wta
    wet
    e202.1
    wth
    wph
    wps
    e202.2
    vd02
    e202.3
    e202.4
    e222
end
