include "vd01.mm"
include "e11.mm"

theorem e10
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume e10.1: |- (. ph ->. ps ).
  assume e10.2: |- ch
  assume e10.3: |- ( ps -> ( ch -> th ) )


  assert |- (. ph ->. th ).

  proof
    wph
    wps
    wch
    wth
    e10.1
    wch
    wph
    e10.2
    vd01
    e10.3
    e11
end
