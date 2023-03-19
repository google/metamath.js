include "vd12.mm"
include "e220.mm"

theorem e120
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume e120.1: |- (. ph ->. ps ).
  assume e120.2: |- (. ph ,. ch ->. th ).
  assume e120.3: |- ta
  assume e120.4: |- ( ps -> ( th -> ( ta -> et ) ) )


  assert |- (. ph ,. ch ->. et ).

  proof
    wph
    wch
    wps
    wth
    wta
    wet
    wph
    wps
    wch
    e120.1
    vd12
    e120.2
    e120.3
    e120.4
    e220
end
