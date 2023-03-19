include "wl-a1i.mm"

theorem wl-impchain-a1-1
  let wph: wff ph
  let wps: wff ps
  assume wl-impchain-a1-1.a: |- ph


  assert |- ( ps -> ph )

  proof
    wph
    wps
    wl-impchain-a1-1.a
    wl-a1i
end
