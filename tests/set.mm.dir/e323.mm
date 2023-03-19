include "dfvd3i.mm"
include "dfvd2i.mm"
include "ee323.mm"
include "dfvd3ir.mm"

theorem e323
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  let wze: wff ze
  assume e323.1: |- (. ph ,. ps ,. ch ->. th ).
  assume e323.2: |- (. ph ,. ps ->. ta ).
  assume e323.3: |- (. ph ,. ps ,. ch ->. et ).
  assume e323.4: |- ( th -> ( ta -> ( et -> ze ) ) )


  assert |- (. ph ,. ps ,. ch ->. ze ).

  proof
    wph
    wps
    wch
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
    wth
    e323.1
    dfvd3i
    wph
    wps
    wta
    e323.2
    dfvd2i
    wph
    wps
    wch
    wet
    e323.3
    dfvd3i
    e323.4
    ee323
    dfvd3ir
end
