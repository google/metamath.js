include "cxr.mm"
include "cxmu.mm"
include "xmulf.mm"
include "fovcl.mm"

theorem xmulcl
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR* /\ B e. RR* ) -> ( A *e B ) e. RR* )

  proof
    cA
    cB
    cxr
    cxr
    cxr
    cxmu
    xmulf
    fovcl
end
