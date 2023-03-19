include "wa.mm"
include "intnanrd.mm"
include "3bior1fd.mm"

theorem 3bior1fand
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume 3biorfd.1: |- ( ph -> -. th )


  assert |- ( ph -> ( ( ch \/ ps ) <-> ( ( th /\ ta ) \/ ch \/ ps ) ) )

  proof
    wph
    wps
    wch
    wth
    wta
    wa
    wph
    wth
    wta
    3biorfd.1
    intnanrd
    3bior1fd
end
