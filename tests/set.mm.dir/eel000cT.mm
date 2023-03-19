include "wtru.mm"
include "mp3an1.mm"
include "mpan.mm"
include "ax-mp.mm"
include "a1i.mm"

theorem eel000cT
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume eel000cT.1: |- ph
  assume eel000cT.2: |- ps
  assume eel000cT.3: |- ch
  assume eel000cT.4: |- ( ( ph /\ ps /\ ch ) -> th )


  assert |- ( T. -> th )

  proof
    wth
    wtru
    wch
    wth
    eel000cT.3
    wps
    wch
    wth
    eel000cT.2
    wph
    wps
    wch
    wth
    eel000cT.1
    eel000cT.4
    mp3an1
    mpan
    ax-mp
    a1i
end
