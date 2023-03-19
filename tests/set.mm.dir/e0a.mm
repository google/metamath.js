include "ax-mp.mm"

theorem e0a
  let wph: wff ph
  let wps: wff ps
  assume e0a.1: |- ph
  assume e0a.2: |- ( ph -> ps )


  assert |- ps

  proof
    wph
    wps
    e0a.1
    e0a.2
    ax-mp
end
