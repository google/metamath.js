include "wcel.mm"
include "wf1o.mm"
include "elsymgbas2.mm"
include "ibi.mm"

theorem symgbasf1o
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


  assert |- ( F e. B -> F : A -1-1-onto-> A )

  proof
    cF
    cB
    wcel
    cA
    cA
    cF
    wf1o
    cA
    cB
    cF
    cG
    cB
    symgbas.1
    symgbas.2
    elsymgbas2
    ibi
end
