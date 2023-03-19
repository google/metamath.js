include "in1.mm"
include "ee1111.mm"
include "dfvd1ir.mm"

theorem e1111
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume e1111.1: |- (. ph ->. ps ).
  assume e1111.2: |- (. ph ->. ch ).
  assume e1111.3: |- (. ph ->. th ).
  assume e1111.4: |- (. ph ->. ta ).
  assume e1111.5: |- ( ps -> ( ch -> ( th -> ( ta -> et ) ) ) )


  assert |- (. ph ->. et ).

  proof
    wph
    wet
    wph
    wps
    wch
    wth
    wta
    wet
    wph
    wps
    e1111.1
    in1
    wph
    wch
    e1111.2
    in1
    wph
    wth
    e1111.3
    in1
    wph
    wta
    e1111.4
    in1
    e1111.5
    ee1111
    dfvd1ir
end
