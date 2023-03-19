include "id.mm"
include "imim12i.mm"

theorem imim1i
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
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
