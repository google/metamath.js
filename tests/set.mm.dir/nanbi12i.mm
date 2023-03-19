include "wb.mm"
include "wnan.mm"
include "nanbi12.mm"
include "mp2an.mm"

theorem nanbi12i
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume nanbii.1: |- ( ph <-> ps )
  assume nanbi12i.2: |- ( ch <-> th )


  assert |- ( ( ph -/\ ch ) <-> ( ps -/\ th ) )

  proof
    wph
    wps
    wb
    wch
    wth
    wb
    wph
    wch
    wnan
    wps
    wth
    wnan
    wb
    nanbii.1
    nanbi12i.2
    wph
    wps
    wch
    wth
    nanbi12
    mp2an
end
