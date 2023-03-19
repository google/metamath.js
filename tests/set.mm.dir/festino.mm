include "wa.mm"
include "wn.mm"
include "wi.mm"
include "spi.mm"
include "con2i.mm"
include "anim2i.mm"
include "eximii.mm"

theorem festino
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  assume festino.maj: |- A. x ( ph -> -. ps )
  assume festino.min: |- E. x ( ch /\ ps )


  assert |- E. x ( ch /\ -. ph )

  proof
    wch
    wps
    wa
    wch
    wph
    wn
    #
    wa
    vx
    festino.min
    wps
    @0
    wch
    wph
    wps
    wph
    wps
    wn
    wi
    vx
    festino.maj
    spi
    con2i
    anim2i
    eximii
end
