include "wb.mm"
include "wi.mm"
include "biimpi.mm"
include "bi33imp12.mm"

theorem bi13imp2
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume bi13imp2.1: |- ( ph <-> ( ps -> ( ch <-> th ) ) )


  assert |- ( ( ph /\ ps /\ ch ) -> th )

  proof
    wph
    wps
    wch
    wth
    wph
    wps
    wch
    wth
    wb
    wi
    bi13imp2.1
    biimpi
    bi33imp12
end
