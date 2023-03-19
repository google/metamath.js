include "wi.mm"
include "imim2i.mm"
include "syl5.mm"

theorem imim12i
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  param wth: wff th
  assume imim12i.1: |- ( ph -> ps )
  assume imim12i.2: |- ( ch -> th )


  assert |- ( ( ps -> ch ) -> ( ph -> th ) )

  proof
    wph
    wps
    wps
    wch
    wi
    wth
    imim12i.1
    wch
    wth
    wps
    imim12i.2
    imim2i
    syl5
end
