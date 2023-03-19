include "wi.mm"
include "a1i.mm"
include "dfvd3ir.mm"

theorem vd03
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume vd03.1: |- ph


  assert |- (. ps ,. ch ,. th ->. ph ).

  proof
    wps
    wch
    wth
    wph
    wch
    wth
    wph
    wi
    #
    wi
    wps
    @0
    wch
    wph
    wth
    vd03.1
    a1i
    a1i
    a1i
    dfvd3ir
end
