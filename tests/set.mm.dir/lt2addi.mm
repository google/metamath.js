include "cr.mm"
include "wcel.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "caddc.mm"
include "co.mm"
include "wi.mm"
include "lt2add.mm"
include "mp4an.mm"

theorem lt2addi
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume lt2.1: |- A e. RR
  assume lt2.2: |- B e. RR
  assume lt2.3: |- C e. RR
  assume lt.4: |- D e. RR


  assert |- ( ( A < C /\ B < D ) -> ( A + B ) < ( C + D ) )

  proof
    cA
    cr
    wcel
    cB
    cr
    wcel
    cC
    cr
    wcel
    cD
    cr
    wcel
    cA
    cC
    clt
    wbr
    cB
    cD
    clt
    wbr
    wa
    cA
    cB
    caddc
    co
    cC
    cD
    caddc
    co
    clt
    wbr
    wi
    lt2.1
    lt2.2
    lt2.3
    lt.4
    cA
    cB
    cC
    cD
    lt2add
    mp4an
end
