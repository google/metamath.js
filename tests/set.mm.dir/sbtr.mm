include "wsb.mm"
include "sbtrt.mm"
include "mpg.mm"

theorem sbtr
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  assume sbtr.nf: |- F/ y ph
  assume sbtr.1: |- [ y / x ] ph


  assert |- ph

  proof
    wph
    vx
    vy
    wsb
    wph
    vy
    wph
    vx
    vy
    sbtr.nf
    sbtrt
    sbtr.1
    mpg
end
