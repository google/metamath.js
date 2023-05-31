include "id.mm"
include "orim12i.mm"

theorem orim2i
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  assume orim1i.1: |- ( ph -> ps )


  assert |- ( ( ch \/ ph ) -> ( ch \/ ps ) )

  proof
    wch
    wch
    wph
    wps
    wch
    id
    orim1i.1
    orim12i
end
