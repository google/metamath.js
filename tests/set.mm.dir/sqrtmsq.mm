include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "csqrt.mm"
include "cfv.mm"
include "cmul.mm"
include "simpl.mm"
include "recnd.mm"
include "sqvald.mm"
include "fveq2d.mm"
include "sqrtsq.mm"
include "eqtr3d.mm"

theorem sqrtmsq
  let cA: class A


  assert |- ( ( A e. RR /\ 0 <_ A ) -> ( sqrt ` ( A x. A ) ) = A )

  proof
    cA
    cr
    wcel
    #
    cc0
    cA
    cle
    wbr
    #
    wa
    #
    cA
    c2
    cexp
    co
    #
    csqrt
    cfv
    cA
    cA
    cmul
    co
    #
    csqrt
    cfv
    cA
    @2
    @3
    @4
    csqrt
    @2
    cA
    @2
    cA
    @0
    @1
    simpl
    recnd
    sqvald
    fveq2d
    cA
    sqrtsq
    eqtr3d
end
