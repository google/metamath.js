include "wn.mm"
include "a1i.mm"
include "mtod.mm"

theorem mtoi
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume mtoi.1: |- -. ch
  assume mtoi.2: |- ( ph -> ( ps -> ch ) )


  assert |- ( ph -> -. ps )

  proof
    wph
    wps
    wch
    wch
    wn
    wph
    mtoi.1
    a1i
    mtoi.2
    mtod
end
