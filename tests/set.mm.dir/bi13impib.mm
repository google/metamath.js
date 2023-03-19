include "wa.mm"
include "wi.mm"
include "biimpi.mm"
include "3impib.mm"

theorem bi13impib
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume bi13impib.1: |- ( ph <-> ( ( ps /\ ch ) -> th ) )


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
    wi
    bi13impib.1
    biimpi
    3impib
end
