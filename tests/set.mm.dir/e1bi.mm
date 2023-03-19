include "biimpi.mm"
include "e1a.mm"

theorem e1bi
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume e1bi.1: |- (. ph ->. ps ).
  assume e1bi.2: |- ( ps <-> ch )


  assert |- (. ph ->. ch ).

  proof
    wph
    wps
    wch
    e1bi.1
    wps
    wch
    e1bi.2
    biimpi
    e1a
end
