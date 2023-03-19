include "wi.mm"
include "wal.mm"
include "copab.mm"
include "wss.mm"
include "ssopab2.mm"
include "ax-gen.mm"
include "mpg.mm"

theorem ssopab2i
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  assume ssopab2i.1: |- ( ph -> ps )


  assert |- { <. x , y >. | ph } C_ { <. x , y >. | ps }

  proof
    wph
    wps
    wi
    #
    vy
    wal
    wph
    vx
    vy
    copab
    wps
    vx
    vy
    copab
    wss
    vx
    wph
    wps
    vx
    vy
    ssopab2
    @0
    vy
    ssopab2i.1
    ax-gen
    mpg
end
