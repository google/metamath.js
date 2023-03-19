include "wn.mm"
include "datisi.mm"

theorem ferison
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  assume ferison.maj: |- A. x ( ph -> -. ps )
  assume ferison.min: |- E. x ( ph /\ ch )


  assert |- E. x ( ch /\ -. ps )

  proof
    wph
    wps
    wn
    wch
    vx
    ferison.maj
    ferison.min
    datisi
end
