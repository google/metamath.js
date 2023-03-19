include "cv.mm"
include "wf1o.mm"
include "f1oeq1.mm"
include "symgbas.mm"
include "elab2g.mm"

theorem elsymgbas2
  let cA: class A
  let cB: class B
  let cF: class F
  let cG: class G
  let cV: class V
  let vf: setvar f
  let vg: setvar g
  let vx: setvar x
  assume symgbas.1: |- G = ( SymGrp ` A )
  assume symgbas.2: |- B = ( Base ` G )


  assert |- ( F e. V -> ( F e. B <-> F : A -1-1-onto-> A ) )

  proof
    cA
    cA
    vx
    cv
    #
    wf1o
    cA
    cA
    cF
    wf1o
    vx
    cF
    cB
    cV
    cA
    cA
    @0
    cF
    f1oeq1
    vx
    cA
    cB
    cG
    symgbas.1
    symgbas.2
    symgbas
    elab2g
end
