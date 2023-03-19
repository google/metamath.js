include "cdm.mm"
include "cxp.mm"
include "wceq.mm"
include "wcel.mm"
include "wa.mm"
include "wn.mm"
include "co.mm"
include "c0.mm"
include "ndmovg.mm"
include "mpan.mm"

theorem ndmov
  let cA: class A
  let cB: class B
  let cS: class S
  let cF: class F
  assume ndmov.1: |- dom F = ( S X. S )


  assert |- ( -. ( A e. S /\ B e. S ) -> ( A F B ) = (/) )

  proof
    cF
    cdm
    cS
    cS
    cxp
    wceq
    cA
    cS
    wcel
    cB
    cS
    wcel
    wa
    wn
    cA
    cB
    cF
    co
    c0
    wceq
    ndmov.1
    cA
    cB
    cS
    cS
    cF
    ndmovg
    mpan
end
