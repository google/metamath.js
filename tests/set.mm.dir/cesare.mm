include "wn.mm"
include "wi.mm"
include "spi.mm"
include "nsyl3.mm"
include "ax-gen.mm"

theorem cesare
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  assume cesare.maj: |- A. x ( ph -> -. ps )
  assume cesare.min: |- A. x ( ch -> ps )


  assert |- A. x ( ch -> -. ph )

  proof
    wch
    wph
    wn
    wi
    vx
    wph
    wps
    wch
    wph
    wps
    wn
    wi
    vx
    cesare.maj
    spi
    wch
    wps
    wi
    vx
    cesare.min
    spi
    nsyl3
    ax-gen
end
