include "wa.mm"
include "wrex.mm"
include "bnj1239.mm"
include "syl.mm"

theorem bnj1299
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let cA: class A
  assume bnj1299.1: |- ( ph -> E. x e. A ( ps /\ ch ) )


  assert |- ( ph -> E. x e. A ps )

  proof
    wph
    wps
    wch
    wa
    vx
    cA
    wrex
    wps
    vx
    cA
    wrex
    bnj1299.1
    wps
    wch
    vx
    cA
    bnj1239
    syl
end
