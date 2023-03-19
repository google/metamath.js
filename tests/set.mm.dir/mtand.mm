include "ex.mm"
include "mtod.mm"

theorem mtand
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume mtand.1: |- ( ph -> -. ch )
  assume mtand.2: |- ( ( ph /\ ps ) -> ch )


  assert |- ( ph -> -. ps )

  proof
    wph
    wps
    wch
    mtand.1
    wph
    wps
    wch
    mtand.2
    ex
    mtod
end
