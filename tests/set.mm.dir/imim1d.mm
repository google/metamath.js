include "idd.mm"
include "imim12d.mm"

theorem imim1d
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  param wth: wff th
  assume imim1d.1: |- ( ph -> ( ps -> ch ) )


  assert |- ( ph -> ( ( ch -> th ) -> ( ps -> th ) ) )

  proof
    wph
    wps
    wch
    wth
    wth
    imim1d.1
    wph
    wth
    idd
    imim12d
end
