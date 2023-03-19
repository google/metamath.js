include "wi.mm"
include "a1i.mm"
include "a2i.mm"

theorem imim2i
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  assume imim2i.1: |- ( ph -> ps )


  assert |- ( ( ch -> ph ) -> ( ch -> ps ) )

  proof
    wch
    wph
    wps
    wph
    wps
    wi
    wch
    imim2i.1
    a1i
    a2i
end
