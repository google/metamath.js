include "anabsi5.mm"
include "ancoms.mm"

theorem anabsi8
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume anabsi8.1: |- ( ps -> ( ( ps /\ ph ) -> ch ) )


  assert |- ( ( ph /\ ps ) -> ch )

  proof
    wps
    wph
    wch
    wps
    wph
    wch
    anabsi8.1
    anabsi5
    ancoms
end
