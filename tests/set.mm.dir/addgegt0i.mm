include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "wa.mm"
include "caddc.mm"
include "co.mm"
include "addgegt0.mm"
include "mpanl12.mm"

theorem addgegt0i
  let cA: class A
  let cB: class B
  assume lt2.1: |- A e. RR
  assume lt2.2: |- B e. RR


  assert |- ( ( 0 <_ A /\ 0 < B ) -> 0 < ( A + B ) )

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
    cB
    clt
    wbr
    wa
    cc0
    cA
    cB
    caddc
    co
    clt
    wbr
    lt2.1
    lt2.2
    cA
    cB
    addgegt0
    mpanl12
end
