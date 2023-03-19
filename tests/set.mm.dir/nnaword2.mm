include "com.mm"
include "wcel.mm"
include "wa.mm"
include "coa.mm"
include "co.mm"
include "nnaword1.mm"
include "nnacom.mm"
include "sseqtrd.mm"

theorem nnaword2
  let cA: class A
  let cB: class B


  assert |- ( ( A e. _om /\ B e. _om ) -> A C_ ( B +o A ) )

  proof
    cA
    com
    wcel
    cB
    com
    wcel
    wa
    cA
    cA
    cB
    coa
    co
    cB
    cA
    coa
    co
    cA
    cB
    nnaword1
    cA
    cB
    nnacom
    sseqtrd
end
