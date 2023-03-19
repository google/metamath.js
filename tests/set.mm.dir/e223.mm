include "wi.mm"
include "in2.mm"
include "in1.mm"
include "in3.mm"
include "ee223.mm"
include "dfvd3ir.mm"

theorem e223
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  let wze: wff ze
  assume e223.1: |- (. ph ,. ps ->. ch ).
  assume e223.2: |- (. ph ,. ps ->. th ).
  assume e223.3: |- (. ph ,. ps ,. ta ->. et ).
  assume e223.4: |- ( ch -> ( th -> ( et -> ze ) ) )


  assert |- (. ph ,. ps ,. ta ->. ze ).

  proof
    wph
    wps
    wta
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
    wi
    wph
    wps
    wch
    e223.1
    in2
    in1
    wph
    wps
    wth
    wi
    wph
    wps
    wth
    e223.2
    in2
    in1
    wph
    wps
    wta
    wet
    wi
    #
    wi
    wph
    wps
    @0
    wph
    wps
    wta
    wet
    e223.3
    in3
    in2
    in1
    e223.4
    ee223
    dfvd3ir
end
