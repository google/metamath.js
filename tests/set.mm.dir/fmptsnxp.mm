include "wcel.mm"
include "wa.mm"
include "csn.mm"
include "cxp.mm"
include "cop.mm"
include "cmpt.mm"
include "xpsng.mm"
include "fmptsn.mm"
include "eqtr2d.mm"

theorem fmptsnxp
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cV: class V
  let cW: class W

  disjoint A x
  disjoint B x
  assert |- ( ( A e. V /\ B e. W ) -> ( x e. { A } |-> B ) = ( { A } X. { B } ) )

  proof
    cA
    cV
    wcel
    cB
    cW
    wcel
    wa
    cA
    csn
    #
    cB
    csn
    cxp
    cA
    cB
    cop
    csn
    vx
    @0
    cB
    cmpt
    cA
    cB
    cV
    cW
    xpsng
    vx
    cA
    cB
    cV
    cW
    fmptsn
    eqtr2d
end
