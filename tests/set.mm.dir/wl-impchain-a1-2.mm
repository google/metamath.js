include "wi.mm"
include "wl-impchain-a1-1.mm"
include "wl-impchain-com-1.2.mm"

theorem wl-impchain-a1-2
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume wl-impchain-a1-2.a: |- ( ph -> ps )


  assert |- ( ph -> ( ch -> ps ) )

  proof
    wps
    wph
    wch
    wph
    wps
    wi
    wch
    wl-impchain-a1-2.a
    wl-impchain-a1-1
    wl-impchain-com-1.2
end
