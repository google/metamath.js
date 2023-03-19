include "trud.mm"
include "sbt.mm"

theorem sbtT
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  assume sbtT.1: |- ( T. -> ph )


  assert |- [ y / x ] ph

  proof
    wph
    vx
    vy
    wph
    sbtT.1
    trud
    sbt
end
