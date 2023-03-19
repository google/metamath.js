include "cxr.mm"
include "cxad.mm"
include "xaddf.mm"
include "fovcl.mm"

theorem xaddcl
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR* /\ B e. RR* ) -> ( A +e B ) e. RR* )

  proof
    cA
    cB
    cxr
    cxr
    cxr
    cxad
    xaddf
    fovcl
end
