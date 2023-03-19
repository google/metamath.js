include "wi.mm"
include "wl-imim2i.mm"
include "wl-impchain-mp-0.mm"

theorem wl-impchain-mp-1
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume wl-impchain-mp-1.a: |- ( ch -> ps )
  assume wl-impchain-mp-1.b: |- ( ps -> ph )


  assert |- ( ch -> ph )

  proof
    wch
    wph
    wi
    wch
    wps
    wi
    wl-impchain-mp-1.a
    wps
    wph
    wch
    wl-impchain-mp-1.b
    wl-imim2i
    wl-impchain-mp-0
end
