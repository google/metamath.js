include "wb.mm"
include "a1d.mm"
include "pm5.32rd.mm"

theorem anbi1d
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume bid.1: |- ( ph -> ( ps <-> ch ) )


  assert |- ( ph -> ( ( ps /\ th ) <-> ( ch /\ th ) ) )

  proof
    wph
    wth
    wps
    wch
    wph
    wps
    wch
    wb
    wth
    bid.1
    a1d
    pm5.32rd
end
