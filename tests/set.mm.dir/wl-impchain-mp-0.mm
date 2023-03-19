include "ax-mp.mm"

theorem wl-impchain-mp-0
  let wph: wff ph
  let wps: wff ps
  assume wl-impchain-mp-0.a: |- ps
  assume wl-impchain-mp-0.b: |- ( ps -> ph )


  assert |- ph

  proof
    wps
    wph
    wl-impchain-mp-0.a
    wl-impchain-mp-0.b
    ax-mp
end
