include "wn.mm"
include "barbara.mm"

theorem celarent
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  assume celarent.maj: |- A. x ( ph -> -. ps )
  assume celarent.min: |- A. x ( ch -> ph )


  assert |- A. x ( ch -> -. ps )

  proof
    wph
    wps
    wn
    wch
    vx
    celarent.maj
    celarent.min
    barbara
end
