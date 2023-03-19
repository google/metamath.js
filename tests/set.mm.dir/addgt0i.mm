include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "caddc.mm"
include "co.mm"
include "addgt0.mm"
include "mpanl12.mm"

theorem addgt0i
  let cA: class A
  let cB: class B
  assume lt2.1: |- A e. RR
  assume lt2.2: |- B e. RR


  assert |- ( ( 0 < A /\ 0 < B ) -> 0 < ( A + B ) )

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
    caddc
    co
    clt
    wbr
    lt2.1
    lt2.2
    cA
    cB
    addgt0
    mpanl12
end
