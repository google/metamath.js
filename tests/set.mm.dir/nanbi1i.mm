include "wb.mm"
include "wnan.mm"
include "nanbi1.mm"
include "ax-mp.mm"

theorem nanbi1i
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume nanbii.1: |- ( ph <-> ps )


  assert |- ( ( ph -/\ ch ) <-> ( ps -/\ ch ) )

  proof
    wph
    wps
    wb
    wph
    wch
    wnan
    wps
    wch
    wnan
    wb
    nanbii.1
    wph
    wps
    wch
    nanbi1
    ax-mp
end
