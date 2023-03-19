include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "cmul.mm"
include "co.mm"
include "cle.mm"
include "wa.mm"
include "prodge0.mm"
include "mpanl12.mm"

theorem prodge0i
  let cA: class A
  let cB: class B
  assume ltplus1.1: |- A e. RR
  assume prodgt0.2: |- B e. RR


  assert |- ( ( 0 < A /\ 0 <_ ( A x. B ) ) -> 0 <_ B )

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
    cA
    cB
    cmul
    co
    cle
    wbr
    wa
    cc0
    cB
    cle
    wbr
    ltplus1.1
    prodgt0.2
    cA
    cB
    prodge0
    mpanl12
end
