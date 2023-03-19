include "wb.mm"
include "a1i.mm"
include "pm5.74i.mm"

theorem imbi2i
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume imbi2i.1: |- ( ph <-> ps )


  assert |- ( ( ch -> ph ) <-> ( ch -> ps ) )

  proof
    wch
    wph
    wps
    wph
    wps
    wb
    wch
    imbi2i.1
    a1i
    pm5.74i
end
