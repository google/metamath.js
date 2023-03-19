include "mp3an1.mm"
include "syl2anc.mm"

theorem mp3an2i
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume mp3an2i.1: |- ph
  assume mp3an2i.2: |- ( ps -> ch )
  assume mp3an2i.3: |- ( ps -> th )
  assume mp3an2i.4: |- ( ( ph /\ ch /\ th ) -> ta )


  assert |- ( ps -> ta )

  proof
    wps
    wch
    wth
    wta
    mp3an2i.2
    mp3an2i.3
    wph
    wch
    wth
    wta
    mp3an2i.1
    mp3an2i.4
    mp3an1
    syl2anc
end
