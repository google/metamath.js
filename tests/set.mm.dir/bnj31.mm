include "wrex.mm"
include "reximi.mm"
include "syl.mm"

theorem bnj31
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let cA: class A
  assume bnj31.1: |- ( ph -> E. x e. A ps )
  assume bnj31.2: |- ( ps -> ch )


  assert |- ( ph -> E. x e. A ch )

  proof
    wph
    wps
    vx
    cA
    wrex
    wch
    vx
    cA
    wrex
    bnj31.1
    wps
    wch
    vx
    cA
    bnj31.2
    reximi
    syl
end
