include "anasss.mm"
include "anabsan2.mm"

theorem anabss3
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume anabss3.1: |- ( ( ( ph /\ ps ) /\ ps ) -> ch )


  assert |- ( ( ph /\ ps ) -> ch )

  proof
    wph
    wps
    wch
    wph
    wps
    wps
    wch
    anabss3.1
    anasss
    anabsan2
end
