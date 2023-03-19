include "wi.mm"
include "wb.mm"
include "biimpi.mm"
include "bi23imp13.mm"

theorem bi12imp3
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume bi12imp3.1: |- ( ph <-> ( ps <-> ( ch -> th ) ) )


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
    wi
    wb
    bi12imp3.1
    biimpi
    bi23imp13
end
