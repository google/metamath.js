include "wn.mm"
include "wi.mm"
include "bj-con2com.mm"
include "ax-mp.mm"

theorem bj-con2comi
  let wph: wff ph
  let wps: wff ps
  assume bj-con2comi.1: |- ph


  assert |- ( ( ps -> -. ph ) -> -. ps )

  proof
    wph
    wps
    wph
    wn
    wi
    wps
    wn
    wi
    bj-con2comi.1
    wph
    wps
    bj-con2com
    ax-mp
end
