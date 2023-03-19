include "wn.mm"
include "barbari.mm"

theorem celaront
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  assume celaront.maj: |- A. x ( ph -> -. ps )
  assume celaront.min: |- A. x ( ch -> ph )
  assume celaront.e: |- E. x ch


  assert |- E. x ( ch /\ -. ps )

  proof
    wph
    wps
    wn
    wch
    vx
    celaront.maj
    celaront.min
    celaront.e
    barbari
end
