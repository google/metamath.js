include "wb.mm"
include "wi.mm"
include "imbi12.mm"
include "mp2.mm"

theorem imbi12i
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume imbi12i.1: |- ( ph <-> ps )
  assume imbi12i.2: |- ( ch <-> th )


  assert |- ( ( ph -> ch ) <-> ( ps -> th ) )

  proof
    wph
    wps
    wb
    wch
    wth
    wb
    wph
    wch
    wi
    wps
    wth
    wi
    wb
    imbi12i.1
    imbi12i.2
    wph
    wps
    wch
    wth
    imbi12
    mp2
end
