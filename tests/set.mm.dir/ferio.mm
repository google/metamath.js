include "wn.mm"
include "darii.mm"

theorem ferio
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  assume ferio.maj: |- A. x ( ph -> -. ps )
  assume ferio.min: |- E. x ( ch /\ ph )


  assert |- E. x ( ch /\ -. ps )

  proof
    wph
    wps
    wn
    wch
    vx
    ferio.maj
    ferio.min
    darii
end
