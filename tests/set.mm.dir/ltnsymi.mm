include "cr.mm"
include "wcel.mm"
include "clt.mm"
include "wbr.mm"
include "wn.mm"
include "wi.mm"
include "ltnsym.mm"
include "mp2an.mm"

theorem ltnsymi
  let cA: class A
  let cB: class B
  assume lt.1: |- A e. RR
  assume lt.2: |- B e. RR


  assert |- ( A < B -> -. B < A )

  proof
    cA
    cr
    wcel
    cB
    cr
    wcel
    cA
    cB
    clt
    wbr
    cB
    cA
    clt
    wbr
    wn
    wi
    lt.1
    lt.2
    cA
    cB
    ltnsym
    mp2an
end
