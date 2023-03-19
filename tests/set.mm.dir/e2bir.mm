include "biimpri.mm"
include "e2.mm"

theorem e2bir
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume e2bir.1: |- (. ph ,. ps ->. ch ).
  assume e2bir.2: |- ( th <-> ch )


  assert |- (. ph ,. ps ->. th ).

  proof
    wph
    wps
    wch
    wth
    e2bir.1
    wth
    wch
    e2bir.2
    biimpri
    e2
end
