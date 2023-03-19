include "vd01.mm"
include "e11.mm"

theorem e01
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume e01.1: |- ph
  assume e01.2: |- (. ps ->. ch ).
  assume e01.3: |- ( ph -> ( ch -> th ) )


  assert |- (. ps ->. th ).

  proof
    wps
    wph
    wch
    wth
    wph
    wps
    e01.1
    vd01
    e01.2
    e01.3
    e11
end
