include "wtru.mm"
include "ax-mp.mm"
include "a1i.mm"

theorem eel0cT
  let wph: wff ph
  let wps: wff ps
  assume eel0cT.1: |- ph
  assume eel0cT.2: |- ( ph -> ps )


  assert |- ( T. -> ps )

  proof
    wps
    wtru
    wph
    wps
    eel0cT.1
    eel0cT.2
    ax-mp
    a1i
end
