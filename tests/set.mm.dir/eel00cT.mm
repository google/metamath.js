include "wtru.mm"
include "mpan.mm"
include "ax-mp.mm"
include "a1i.mm"

theorem eel00cT
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume eel00cT.1: |- ph
  assume eel00cT.2: |- ps
  assume eel00cT.3: |- ( ( ph /\ ps ) -> ch )


  assert |- ( T. -> ch )

  proof
    wch
    wtru
    wps
    wch
    eel00cT.2
    wph
    wps
    wch
    eel00cT.1
    eel00cT.3
    mpan
    ax-mp
    a1i
end
