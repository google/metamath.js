include "cxr.mm"
include "cico.mm"
include "dmico.mm"
include "ndmov.mm"

theorem ndmico
  let cA: class A
  let cB: class B


  assert |- ( -. ( A e. RR* /\ B e. RR* ) -> ( A [,) B ) = (/) )

  proof
    cA
    cB
    cxr
    cico
    dmico
    ndmov
end
