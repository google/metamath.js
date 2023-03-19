include "cc.mm"
include "wcel.mm"
include "wa.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "csqrt.mm"
include "cfv.mm"
include "wceq.mm"
include "cneg.mm"
include "wo.mm"
include "sqrtth.mm"
include "adantl.mm"
include "eqeq2d.mm"
include "wb.mm"
include "sqrtcl.mm"
include "sqeqor.mm"
include "sylan2.mm"
include "bitr3d.mm"

theorem eqsqrtor
  let cA: class A
  let cB: class B


  assert |- ( ( A e. CC /\ B e. CC ) -> ( ( A ^ 2 ) = B <-> ( A = ( sqrt ` B ) \/ A = -u ( sqrt ` B ) ) ) )

  proof
    cA
    cc
    wcel
    #
    cB
    cc
    wcel
    #
    wa
    #
    cA
    c2
    cexp
    co
    #
    cB
    csqrt
    cfv
    #
    c2
    cexp
    co
    #
    wceq
    #
    @3
    cB
    wceq
    cA
    @4
    wceq
    cA
    @4
    cneg
    wceq
    wo
    #
    @2
    @5
    cB
    @3
    @1
    @5
    cB
    wceq
    @0
    cB
    sqrtth
    adantl
    eqeq2d
    @1
    @0
    @4
    cc
    wcel
    @6
    @7
    wb
    cB
    sqrtcl
    cA
    @4
    sqeqor
    sylan2
    bitr3d
end
