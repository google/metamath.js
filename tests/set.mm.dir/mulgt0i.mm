include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "cmul.mm"
include "co.mm"
include "wi.mm"
include "axmulgt0.mm"
include "mp2an.mm"

theorem mulgt0i
  let cA: class A
  let cB: class B
  assume lt.1: |- A e. RR
  assume lt.2: |- B e. RR


  assert |- ( ( 0 < A /\ 0 < B ) -> 0 < ( A x. B ) )

  proof
    cA
    cr
    wcel
    cB
    cr
    wcel
    cc0
    cA
    clt
    wbr
    cc0
    cB
    clt
    wbr
    wa
    cc0
    cA
    cB
    cmul
    co
    clt
    wbr
    wi
    lt.1
    lt.2
    cA
    cB
    axmulgt0
    mp2an
end
