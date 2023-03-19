include "wcel.mm"
include "wf1o.mm"
include "wf.mm"
include "symgbasf1o.mm"
include "f1of.mm"
include "syl.mm"

theorem symgbasf
  let cA: class A
  let cB: class B
  let cF: class F
  let cG: class G
  let vf: setvar f
  let vg: setvar g
  let vx: setvar x
  let cV: class V
  assume symgbas.1: |- G = ( SymGrp ` A )
  assume symgbas.2: |- B = ( Base ` G )


  assert |- ( F e. B -> F : A --> A )

  proof
    cF
    cB
    wcel
    cA
    cA
    cF
    wf1o
    cA
    cA
    cF
    wf
    cA
    cB
    cF
    cG
    symgbas.1
    symgbas.2
    symgbasf1o
    cA
    cA
    cF
    f1of
    syl
end
