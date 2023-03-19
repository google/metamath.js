include "cop.mm"
include "wcel.mm"
include "wfn.mm"
include "wbr.mm"
include "df-br.mm"
include "fnbr.mm"
include "sylan2br.mm"

theorem fnop
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F


  assert |- ( ( F Fn A /\ <. B , C >. e. F ) -> B e. A )

  proof
    cB
    cC
    cop
    cF
    wcel
    cF
    cA
    wfn
    cB
    cC
    cF
    wbr
    cB
    cA
    wcel
    cB
    cC
    cF
    df-br
    cA
    cB
    cC
    cF
    fnbr
    sylan2br
end
