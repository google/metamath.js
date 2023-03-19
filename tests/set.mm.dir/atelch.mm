include "cat.mm"
include "cch.mm"
include "atssch.mm"
include "sseli.mm"

theorem atelch
  let cA: class A
  let vx: setvar x
  let cB: class B


  assert |- ( A e. HAtoms -> A e. CH )

  proof
    cat
    cch
    cA
    atssch
    sseli
end
