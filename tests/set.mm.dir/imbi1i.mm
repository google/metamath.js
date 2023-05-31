include "wb.mm"
include "wi.mm"
include "imbi1.mm"
include "ax-mp.mm"

theorem imbi1i
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
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
