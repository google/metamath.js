include "wsb.mm"
include "stdpc4.mm"
include "mpg.mm"

theorem sbt
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  assume sbt.1: |- ph


  assert |- [ y / x ] ph

  proof
    wph
    wph
    vx
    vy
    wsb
    vx
    wph
    vx
    vy
    stdpc4
    sbt.1
    mpg
end
