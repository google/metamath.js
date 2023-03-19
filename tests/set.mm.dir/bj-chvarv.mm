include "weq.mm"
include "biimpd.mm"
include "spimv1.mm"
include "mpg.mm"

theorem bj-chvarv
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  assume bj-chvarv.nf: |- F/ x ps
  assume bj-chvarv.1: |- ( x = y -> ( ph <-> ps ) )
  assume bj-chvarv.2: |- ph

  disjoint x y
  assert |- ps

  proof
    wph
    wps
    vx
    wph
    wps
    vx
    vy
    bj-chvarv.nf
    vx
    vy
    weq
    wph
    wps
    bj-chvarv.1
    biimpd
    spimv1
    bj-chvarv.2
    mpg
end
