include "idd.mm"
include "imim12d.mm"

theorem imim1d
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
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
