include "an12s.mm"
include "anabss7.mm"

theorem anabsan2
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume anabsan2.1: |- ( ( ph /\ ( ps /\ ps ) ) -> ch )


  assert |- ( ( ph /\ ps ) -> ch )

  proof
    wph
    wps
    wch
    wph
    wps
    wps
    wch
    anabsan2.1
    an12s
    anabss7
end
