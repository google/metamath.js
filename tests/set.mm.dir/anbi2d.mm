include "wb.mm"
include "a1d.mm"
include "pm5.32d.mm"

theorem anbi2d
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  param wth: wff th
  assume bid.1: |- ( ph -> ( ps <-> ch ) )


  assert |- ( ph -> ( ( th /\ ps ) <-> ( th /\ ch ) ) )

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
    pm5.32d
end
