include "mp3an12.mm"
include "syl.mm"

theorem mp3an12i
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume mp3an12i.1: |- ph
  assume mp3an12i.2: |- ps
  assume mp3an12i.3: |- ( ch -> th )
  assume mp3an12i.4: |- ( ( ph /\ ps /\ th ) -> ta )


  assert |- ( ch -> ta )

  proof
    wch
    wth
    wta
    mp3an12i.3
    wph
    wps
    wth
    wta
    mp3an12i.1
    mp3an12i.2
    mp3an12i.4
    mp3an12
    syl
end
