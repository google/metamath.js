include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "csqrt.mm"
include "cfv.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "cmul.mm"
include "resqrtcl.mm"
include "recnd.mm"
include "sqvald.mm"
include "resqrtth.mm"
include "eqtr3d.mm"

theorem remsqsqrt
  let cA: class A


  assert |- ( ( A e. RR /\ 0 <_ A ) -> ( ( sqrt ` A ) x. ( sqrt ` A ) ) = A )

  proof
    cA
    cr
    wcel
    cc0
    cA
    cle
    wbr
    wa
    #
    cA
    csqrt
    cfv
    #
    c2
    cexp
    co
    @1
    @1
    cmul
    co
    cA
    @0
    @1
    @0
    @1
    cA
    resqrtcl
    recnd
    sqvald
    cA
    resqrtth
    eqtr3d
end
