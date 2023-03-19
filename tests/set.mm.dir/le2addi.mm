include "cr.mm"
include "wcel.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "caddc.mm"
include "co.mm"
include "wi.mm"
include "le2add.mm"
include "mp4an.mm"

theorem le2addi
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume lt2.1: |- A e. RR
  assume lt2.2: |- B e. RR
  assume lt2.3: |- C e. RR
  assume lt.4: |- D e. RR


  assert |- ( ( A <_ C /\ B <_ D ) -> ( A + B ) <_ ( C + D ) )

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
    cle
    wbr
    cB
    cD
    cle
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
    cle
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
    le2add
    mp4an
end
