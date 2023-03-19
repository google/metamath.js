include "wnf.mm"
include "wn.mm"
include "nfnt.mm"
include "syl.mm"

theorem nfnd
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  assume nfnd.1: |- ( ph -> F/ x ps )


  assert |- ( ph -> F/ x -. ps )

  proof
    wph
    wps
    vx
    wnf
    wps
    wn
    vx
    wnf
    nfnd.1
    wps
    vx
    nfnt
    syl
end
