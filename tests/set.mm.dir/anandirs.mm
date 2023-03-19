include "wa.mm"
include "an4s.mm"
include "anabsan2.mm"

theorem anandirs
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wta: wff ta
  assume anandirs.1: |- ( ( ( ph /\ ch ) /\ ( ps /\ ch ) ) -> ta )


  assert |- ( ( ( ph /\ ps ) /\ ch ) -> ta )

  proof
    wph
    wps
    wa
    wch
    wta
    wph
    wch
    wps
    wch
    wta
    anandirs.1
    an4s
    anabsan2
end
