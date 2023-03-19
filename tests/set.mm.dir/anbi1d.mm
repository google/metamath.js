include "wb.mm"
include "a1d.mm"
include "pm5.32rd.mm"

theorem anbi1d
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  param wth: wff th
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
