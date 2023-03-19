include "wcel.mm"
include "symgbasf.mm"
include "ffvelrnda.mm"

theorem symgfv
  let cA: class A
  let cB: class B
  let cF: class F
  let cG: class G
  let cX: class X
  let vf: setvar f
  let vg: setvar g
  let vx: setvar x
  let cV: class V
  assume symgbas.1: |- G = ( SymGrp ` A )
  assume symgbas.2: |- B = ( Base ` G )


  assert |- ( ( F e. B /\ X e. A ) -> ( F ` X ) e. A )

  proof
    cF
    cB
    wcel
    cA
    cA
    cX
    cF
    cA
    cB
    cF
    cG
    symgbas.1
    symgbas.2
    symgbasf
    ffvelrnda
end
