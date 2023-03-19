include "vd01.mm"
include "e211.mm"

theorem e201
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume e201.1: |- (. ph ,. ps ->. ch ).
  assume e201.2: |- th
  assume e201.3: |- (. ph ->. ta ).
  assume e201.4: |- ( ch -> ( th -> ( ta -> et ) ) )


  assert |- (. ph ,. ps ->. et ).

  proof
    wph
    wps
    wch
    wth
    wta
    wet
    e201.1
    wth
    wph
    e201.2
    vd01
    e201.3
    e201.4
    e211
end
