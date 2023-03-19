include "dfvd2i.mm"
include "syl6.mm"
include "dfvd2ir.mm"

theorem e2
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume e2.1: |- (. ph ,. ps ->. ch ).
  assume e2.2: |- ( ch -> th )


  assert |- (. ph ,. ps ->. th ).

  proof
    wph
    wps
    wth
    wph
    wps
    wch
    wth
    wph
    wps
    wch
    e2.1
    dfvd2i
    e2.2
    syl6
    dfvd2ir
end
