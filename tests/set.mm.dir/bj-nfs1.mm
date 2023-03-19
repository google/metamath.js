include "wnf.mm"
include "wsb.mm"
include "bj-nfs1t2.mm"
include "mpg.mm"

theorem bj-nfs1
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  assume bj-nfs1.nf: |- F/ y ph


  assert |- F/ x [ y / x ] ph

  proof
    wph
    vy
    wnf
    wph
    vx
    vy
    wsb
    vx
    wnf
    vx
    wph
    vx
    vy
    bj-nfs1t2
    bj-nfs1.nf
    mpg
end
