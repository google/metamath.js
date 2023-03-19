include "wn.mm"
include "wi.mm"
include "spi.mm"
include "con2i.mm"
include "nsyl.mm"
include "ax-gen.mm"

theorem calemes
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  assume calemes.maj: |- A. x ( ph -> ps )
  assume calemes.min: |- A. x ( ps -> -. ch )


  assert |- A. x ( ch -> -. ph )

  proof
    wch
    wph
    wn
    wi
    vx
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
    calemes.min
    spi
    con2i
    wph
    wps
    wi
    vx
    calemes.maj
    spi
    nsyl
    ax-gen
end
