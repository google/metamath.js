include "ex.mm"
include "com12.mm"

theorem expcom
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  assume ex.1: |- ( ( ph /\ ps ) -> ch )


  assert |- ( ps -> ( ph -> ch ) )

  proof
    wph
    wps
    wch
    wph
    wps
    wch
    ex.1
    ex
    com12
end
