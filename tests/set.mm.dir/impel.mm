include "syl5.mm"
include "imp.mm"

theorem impel
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume impel.1: |- ( ph -> ( ps -> ch ) )
  assume impel.2: |- ( th -> ps )


  assert |- ( ( ph /\ th ) -> ch )

  proof
    wph
    wth
    wch
    wth
    wps
    wph
    wch
    impel.2
    impel.1
    syl5
    imp
end
