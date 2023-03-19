include "wa.mm"
include "simpl.mm"
include "reximi.mm"

theorem bnj1239
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let cA: class A


  assert |- ( E. x e. A ( ps /\ ch ) -> E. x e. A ps )

  proof
    wps
    wch
    wa
    wps
    vx
    cA
    wps
    wch
    simpl
    reximi
end
