include "an32s.mm"
include "anabsan.mm"

theorem anabss1
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume anabss1.1: |- ( ( ( ph /\ ps ) /\ ph ) -> ch )


  assert |- ( ( ph /\ ps ) -> ch )

  proof
    wph
    wps
    wch
    wph
    wps
    wph
    wch
    anabss1.1
    an32s
    anabsan
end
