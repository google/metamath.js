include "ax-mp.mm"
include "a1i.mm"

theorem mp1i
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume mp1i.1: |- ph
  assume mp1i.2: |- ( ph -> ps )


  assert |- ( ch -> ps )

  proof
    wps
    wch
    wph
    wps
    mp1i.1
    mp1i.2
    ax-mp
    a1i
end
