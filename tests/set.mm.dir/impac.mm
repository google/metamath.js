include "wa.mm"
include "ancrd.mm"
include "imp.mm"

theorem impac
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume impac.1: |- ( ph -> ( ps -> ch ) )


  assert |- ( ( ph /\ ps ) -> ( ch /\ ps ) )

  proof
    wph
    wps
    wch
    wps
    wa
    wph
    wps
    wch
    impac.1
    ancrd
    imp
end
