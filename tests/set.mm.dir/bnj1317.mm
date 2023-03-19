include "cab.mm"
include "hbab1.mm"
include "hbxfreq.mm"

theorem bnj1317
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  assume bnj1317.1: |- A = { x | ph }

  disjoint x y
  assert |- ( y e. A -> A. x y e. A )

  proof
    vx
    vy
    cA
    wph
    vx
    cab
    bnj1317.1
    wph
    vx
    vy
    hbab1
    hbxfreq
end
