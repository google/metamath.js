include "wn.mm"
include "wa.mm"
include "wi.mm"
include "spi.mm"
include "con3i.mm"
include "anim2i.mm"
include "eximii.mm"

theorem baroco
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  assume baroco.maj: |- A. x ( ph -> ps )
  assume baroco.min: |- E. x ( ch /\ -. ps )


  assert |- E. x ( ch /\ -. ph )

  proof
    wch
    wps
    wn
    #
    wa
    wch
    wph
    wn
    #
    wa
    vx
    baroco.min
    @0
    @1
    wch
    wph
    wps
    wph
    wps
    wi
    vx
    baroco.maj
    spi
    con3i
    anim2i
    eximii
end
