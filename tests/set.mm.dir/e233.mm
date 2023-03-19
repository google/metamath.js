include "dfvd2i.mm"
include "dfvd3i.mm"
include "ee233.mm"
include "dfvd3ir.mm"

theorem e233
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  let wze: wff ze
  assume e233.1: |- (. ph ,. ps ->. ch ).
  assume e233.2: |- (. ph ,. ps ,. th ->. ta ).
  assume e233.3: |- (. ph ,. ps ,. th ->. et ).
  assume e233.4: |- ( ch -> ( ta -> ( et -> ze ) ) )


  assert |- (. ph ,. ps ,. th ->. ze ).

  proof
    wph
    wps
    wth
    wze
    wph
    wps
    wch
    wth
    wta
    wet
    wze
    wph
    wps
    wch
    e233.1
    dfvd2i
    wph
    wps
    wth
    wta
    e233.2
    dfvd3i
    wph
    wps
    wth
    wet
    e233.3
    dfvd3i
    e233.4
    ee233
    dfvd3ir
end
