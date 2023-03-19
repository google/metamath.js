include "wsb.mm"
include "nf5ri.mm"
include "hbsb3.mm"
include "nf5i.mm"

theorem nfs1
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  assume nfs1.1: |- F/ y ph


  assert |- F/ x [ y / x ] ph

  proof
    wph
    vx
    vy
    wsb
    vx
    wph
    vx
    vy
    wph
    vy
    nfs1.1
    nf5ri
    hbsb3
    nf5i
end
