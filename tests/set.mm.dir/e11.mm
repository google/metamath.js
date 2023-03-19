include "wi.mm"
include "a1i.mm"
include "e111.mm"

theorem e11
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume e11.1: |- (. ph ->. ps ).
  assume e11.2: |- (. ph ->. ch ).
  assume e11.3: |- ( ps -> ( ch -> th ) )


  assert |- (. ph ->. th ).

  proof
    wph
    wps
    wps
    wch
    wth
    e11.1
    e11.1
    e11.2
    wps
    wch
    wth
    wi
    wi
    wps
    e11.3
    a1i
    e111
end
