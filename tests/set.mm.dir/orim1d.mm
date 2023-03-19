include "idd.mm"
include "orim12d.mm"

theorem orim1d
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume orim1d.1: |- ( ph -> ( ps -> ch ) )


  assert |- ( ph -> ( ( ps \/ th ) -> ( ch \/ th ) ) )

  proof
    wph
    wps
    wch
    wth
    wth
    orim1d.1
    wph
    wth
    idd
    orim12d
end
