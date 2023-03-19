include "cfn.mm"
include "wcel.mm"
include "chash.mm"
include "cfv.mm"
include "cv.mm"
include "wf1o.mm"
include "cab.mm"
include "cfa.mm"
include "symgbas.mm"
include "fveq2i.mm"
include "hashfac.mm"
include "syl5eq.mm"

theorem symghash
  let cA: class A
  let cB: class B
  let cG: class G
  let vf: setvar f
  let vg: setvar g
  let vx: setvar x
  let cF: class F
  let cV: class V
  assume symgbas.1: |- G = ( SymGrp ` A )
  assume symgbas.2: |- B = ( Base ` G )


  assert |- ( A e. Fin -> ( # ` B ) = ( ! ` ( # ` A ) ) )

  proof
    cA
    cfn
    wcel
    cB
    chash
    cfv
    cA
    cA
    vf
    cv
    wf1o
    vf
    cab
    #
    chash
    cfv
    cA
    chash
    cfv
    cfa
    cfv
    cB
    @0
    chash
    vf
    cA
    cB
    cG
    symgbas.1
    symgbas.2
    symgbas
    fveq2i
    cA
    vf
    hashfac
    syl5eq
end
