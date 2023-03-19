include "wb.mm"
include "a1d.mm"
include "pm5.32d.mm"

theorem anbi2d
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
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
