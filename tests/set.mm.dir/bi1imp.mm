include "wi.mm"
include "biimpi.mm"
include "imp.mm"

theorem bi1imp
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume bi1imp.1: |- ( ph <-> ( ps -> ch ) )


  assert |- ( ( ph /\ ps ) -> ch )

  proof
    wph
    wps
    wch
    wph
    wps
    wch
    wi
    bi1imp.1
    biimpi
    imp
end
