include "wceq.mm"
include "wal.mm"
include "csb.mm"
include "csbeq2.mm"
include "csbeq1.mm"
include "sylan9eqr.mm"

theorem csbeq12
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- ( ( A = B /\ A. x C = D ) -> [_ A / x ]_ C = [_ B / x ]_ D )

  proof
    cC
    cD
    wceq
    vx
    wal
    cA
    cB
    wceq
    vx
    cA
    cC
    csb
    vx
    cA
    cD
    csb
    vx
    cB
    cD
    csb
    vx
    cA
    cC
    cD
    csbeq2
    vx
    cA
    cB
    cD
    csbeq1
    sylan9eqr
end
