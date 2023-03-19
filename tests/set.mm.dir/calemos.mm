include "wn.mm"
include "wa.mm"
include "wi.mm"
include "spi.mm"
include "con2i.mm"
include "nsyl.mm"
include "ancli.mm"
include "eximii.mm"

theorem calemos
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  assume calemos.maj: |- A. x ( ph -> ps )
  assume calemos.min: |- A. x ( ps -> -. ch )
  assume calemos.e: |- E. x ch


  assert |- E. x ( ch /\ -. ph )

  proof
    wch
    wch
    wph
    wn
    #
    wa
    vx
    calemos.e
    wch
    @0
    wch
    wps
    wph
    wps
    wch
    wps
    wch
    wn
    wi
    vx
    calemos.min
    spi
    con2i
    wph
    wps
    wi
    vx
    calemos.maj
    spi
    nsyl
    ancli
    eximii
end
