include "wi.mm"
include "wnan.mm"
include "naim2.mm"
include "mp2.mm"

theorem naim2i
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume naim2i.1: |- ( ph -> ps )
  assume naim2i.2: |- ( ch -/\ ps )


  assert |- ( ch -/\ ph )

  proof
    wph
    wps
    wi
    wch
    wps
    wnan
    wch
    wph
    wnan
    naim2i.1
    naim2i.2
    wph
    wps
    wch
    naim2
    mp2
end
