include "wi.mm"
include "wnan.mm"
include "naim1.mm"
include "mp2.mm"

theorem naim1i
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume naim1i.1: |- ( ph -> ps )
  assume naim1i.2: |- ( ps -/\ ch )


  assert |- ( ph -/\ ch )

  proof
    wph
    wps
    wi
    wps
    wch
    wnan
    wph
    wch
    wnan
    naim1i.1
    naim1i.2
    wph
    wps
    wch
    naim1
    mp2
end
