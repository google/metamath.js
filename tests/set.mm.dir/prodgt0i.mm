include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "cmul.mm"
include "co.mm"
include "clt.mm"
include "wa.mm"
include "prodgt0.mm"
include "mpanl12.mm"

theorem prodgt0i
  let cA: class A
  let cB: class B
  assume ltplus1.1: |- A e. RR
  assume prodgt0.2: |- B e. RR


  assert |- ( ( 0 <_ A /\ 0 < ( A x. B ) ) -> 0 < B )

  proof
    cA
    cr
    wcel
    cB
    cr
    wcel
    cc0
    cA
    cle
    wbr
    cc0
    cA
    cB
    cmul
    co
    clt
    wbr
    wa
    cc0
    cB
    clt
    wbr
    ltplus1.1
    prodgt0.2
    cA
    cB
    prodgt0
    mpanl12
end
