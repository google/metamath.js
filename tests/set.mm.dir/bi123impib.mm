include "wa.mm"
include "wb.mm"
include "biimpi.mm"
include "bi23impib.mm"

theorem bi123impib
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume bi123impib.1: |- ( ph <-> ( ( ps /\ ch ) <-> th ) )


  assert |- ( ( ph /\ ps /\ ch ) -> th )

  proof
    wph
    wps
    wch
    wth
    wph
    wps
    wch
    wa
    wth
    wb
    bi123impib.1
    biimpi
    bi23impib
end
