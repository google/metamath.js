include "wn.mm"
include "wi.mm"
include "spi.mm"
include "nsyl.mm"
include "ax-gen.mm"

theorem camestres
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  assume camestres.maj: |- A. x ( ph -> ps )
  assume camestres.min: |- A. x ( ch -> -. ps )


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
    wch
    wps
    wn
    wi
    vx
    camestres.min
    spi
    wph
    wps
    wi
    vx
    camestres.maj
    spi
    nsyl
    ax-gen
end
