include "wn.mm"
include "wi.mm"
include "con4.mm"
include "ax-mp.mm"

theorem bj-con4iALT
  let wph: wff ph
  let wps: wff ps
  assume bj-con4iALT.1: |- ( -. ph -> -. ps )


  assert |- ( ps -> ph )

  proof
    wph
    wn
    wps
    wn
    wi
    wps
    wph
    wi
    bj-con4iALT.1
    wph
    wps
    con4
    ax-mp
end
