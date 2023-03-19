include "wb.mm"
include "bicom1.mm"
include "ax-mp.mm"

theorem bicomi
  let wph: wff ph
  let wps: wff ps
  assume bicomi.1: |- ( ph <-> ps )


  assert |- ( ps <-> ph )

  proof
    wph
    wps
    wb
    wps
    wph
    wb
    bicomi.1
    wph
    wps
    bicom1
    ax-mp
end
