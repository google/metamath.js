include "wb.mm"
include "wi.mm"
include "biimp.mm"
include "ax-mp.mm"

theorem biimpi
  let wph: wff ph
  let wps: wff ps
  assume biimpi.1: |- ( ph <-> ps )


  assert |- ( ph -> ps )

  proof
    wph
    wps
    wb
    wph
    wps
    wi
    biimpi.1
    wph
    wps
    biimp
    ax-mp
end
