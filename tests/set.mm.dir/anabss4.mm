include "anabss1.mm"
include "ancoms.mm"

theorem anabss4
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume anabss4.1: |- ( ( ( ps /\ ph ) /\ ps ) -> ch )


  assert |- ( ( ph /\ ps ) -> ch )

  proof
    wps
    wph
    wch
    wps
    wph
    wch
    anabss4.1
    anabss1
    ancoms
end
