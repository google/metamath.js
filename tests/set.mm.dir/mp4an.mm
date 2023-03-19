include "wa.mm"
include "pm3.2i.mm"
include "mp2an.mm"

theorem mp4an
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume mp4an.1: |- ph
  assume mp4an.2: |- ps
  assume mp4an.3: |- ch
  assume mp4an.4: |- th
  assume mp4an.5: |- ( ( ( ph /\ ps ) /\ ( ch /\ th ) ) -> ta )


  assert |- ta

  proof
    wph
    wps
    wa
    wch
    wth
    wa
    wta
    wph
    wps
    mp4an.1
    mp4an.2
    pm3.2i
    wch
    wth
    mp4an.3
    mp4an.4
    pm3.2i
    mp4an.5
    mp2an
end
