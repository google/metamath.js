include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "caddc.mm"
include "co.mm"
include "addge0.mm"
include "mpanl12.mm"

theorem addge0i
  let cA: class A
  let cB: class B
  assume lt2.1: |- A e. RR
  assume lt2.2: |- B e. RR


  assert |- ( ( 0 <_ A /\ 0 <_ B ) -> 0 <_ ( A + B ) )

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
    cle
    wbr
    wa
    cc0
    cA
    cB
    caddc
    co
    cle
    wbr
    lt2.1
    lt2.2
    cA
    cB
    addge0
    mpanl12
end
