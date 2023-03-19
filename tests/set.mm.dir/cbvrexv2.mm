include "nfcv.mm"
include "nfv.mm"
include "cbvrexcsf.mm"

theorem cbvrexv2
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  assume cbvralv2.1: |- ( x = y -> ( ps <-> ch ) )
  assume cbvralv2.2: |- ( x = y -> A = B )

  disjoint A y
  disjoint ps y
  disjoint B x
  disjoint ch x
  assert |- ( E. x e. A ps <-> E. y e. B ch )

  proof
    wps
    wch
    vx
    vy
    cA
    cB
    vy
    cA
    nfcv
    vx
    cB
    nfcv
    wps
    vy
    nfv
    wch
    vx
    nfv
    cbvralv2.2
    cbvralv2.1
    cbvrexcsf
end
