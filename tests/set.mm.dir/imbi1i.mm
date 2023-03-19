include "wb.mm"
include "wi.mm"
include "imbi1.mm"
include "ax-mp.mm"

theorem imbi1i
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume imbi1i.1: |- ( ph <-> ps )


  assert |- ( ( ph -> ch ) <-> ( ps -> ch ) )

  proof
    wph
    wps
    wb
    wph
    wch
    wi
    wps
    wch
    wi
    wb
    imbi1i.1
    wph
    wps
    wch
    imbi1
    ax-mp
end
