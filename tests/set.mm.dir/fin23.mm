include "cfin3.mm"
include "isf33lem.mm"
include "fin23lem40.mm"

theorem fin23
  let cA: class A
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let vf: setvar f
  let vg: setvar g
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cV: class V


  assert |- ( A e. Fin2 -> A e. Fin3 )

  proof
    vx
    cA
    vg
    cfin3
    va
    vx
    vg
    va
    isf33lem
    fin23lem40
end
