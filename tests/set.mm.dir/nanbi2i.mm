include "wb.mm"
include "wnan.mm"
include "nanbi2.mm"
include "ax-mp.mm"

theorem nanbi2i
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume nanbii.1: |- ( ph <-> ps )


  assert |- ( ( ch -/\ ph ) <-> ( ch -/\ ps ) )

  proof
    wph
    wps
    wb
    wch
    wph
    wnan
    wch
    wps
    wnan
    wb
    nanbii.1
    wph
    wps
    wch
    nanbi2
    ax-mp
end
