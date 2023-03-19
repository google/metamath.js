include "cee.mm"
include "cfv.mm"
include "wcel.mm"
include "c1.mm"
include "cfz.mm"
include "co.mm"
include "wfn.mm"
include "wceq.mm"
include "cv.mm"
include "wral.mm"
include "wb.mm"
include "cr.mm"
include "wf.mm"
include "eleei.mm"
include "ffn.mm"
include "syl.mm"
include "eqfnfv.mm"
include "syl2an.mm"

theorem eqeefv
  let cA: class A
  let cB: class B
  let vi: setvar i
  let cN: class N

  disjoint A i
  disjoint B i
  disjoint N i
  assert |- ( ( A e. ( EE ` N ) /\ B e. ( EE ` N ) ) -> ( A = B <-> A. i e. ( 1 ... N ) ( A ` i ) = ( B ` i ) ) )

  proof
    cA
    cN
    cee
    cfv
    #
    wcel
    #
    cA
    c1
    cN
    cfz
    co
    #
    wfn
    #
    cB
    @2
    wfn
    #
    cA
    cB
    wceq
    vi
    cv
    #
    cA
    cfv
    @5
    cB
    cfv
    wceq
    vi
    @2
    wral
    wb
    cB
    @0
    wcel
    #
    @1
    @2
    cr
    cA
    wf
    @3
    cA
    cN
    eleei
    @2
    cr
    cA
    ffn
    syl
    @6
    @2
    cr
    cB
    wf
    @4
    cB
    cN
    eleei
    @2
    cr
    cB
    ffn
    syl
    vi
    @2
    cA
    cB
    eqfnfv
    syl2an
end
