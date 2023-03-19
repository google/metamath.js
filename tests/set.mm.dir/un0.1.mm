include "wtru.mm"
include "in1.mm"
include "dfvd2ani.mm"
include "uun0.1.mm"
include "dfvd1ir.mm"

theorem un0.1
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume un0.1.1: |- (. T. ->. ph ).
  assume un0.1.2: |- (. ps ->. ch ).
  assume un0.1.3: |- (. (. T. ,. ps ). ->. th ).


  assert |- (. ps ->. th ).

  proof
    wps
    wth
    wph
    wps
    wch
    wth
    wtru
    wph
    un0.1.1
    in1
    wps
    wch
    un0.1.2
    in1
    wtru
    wps
    wth
    un0.1.3
    dfvd2ani
    uun0.1
    dfvd1ir
end
