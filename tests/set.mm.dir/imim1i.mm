include "id.mm"
include "imim12i.mm"

theorem imim1i
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  assume imim1i.1: |- ( ph -> ps )


  assert |- ( ( ps -> ch ) -> ( ph -> ch ) )

  proof
    wph
    wps
    wch
    wch
    imim1i.1
    wch
    id
    imim12i
end
