include "anabsi6.mm"
include "ancoms.mm"

theorem anabsi7
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume anabsi7.1: |- ( ps -> ( ( ph /\ ps ) -> ch ) )


  assert |- ( ( ph /\ ps ) -> ch )

  proof
    wps
    wph
    wch
    wps
    wph
    wch
    anabsi7.1
    anabsi6
    ancoms
end
