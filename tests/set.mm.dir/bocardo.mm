include "wn.mm"
include "disamis.mm"

theorem bocardo
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  assume bocardo.maj: |- E. x ( ph /\ -. ps )
  assume bocardo.min: |- A. x ( ph -> ch )


  assert |- E. x ( ch /\ -. ps )

  proof
    wph
    wps
    wn
    wch
    vx
    bocardo.maj
    bocardo.min
    disamis
end
