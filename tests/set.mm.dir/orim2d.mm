include "idd.mm"
include "orim12d.mm"

theorem orim2d
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume orim1d.1: |- ( ph -> ( ps -> ch ) )


  assert |- ( ph -> ( ( th \/ ps ) -> ( th \/ ch ) ) )

  proof
    wph
    wth
    wth
    wps
    wch
    wph
    wth
    idd
    orim1d.1
    orim12d
end
