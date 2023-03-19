include "cr.mm"
include "wcel.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "wi.mm"
include "letr.mm"
include "mp3an.mm"

theorem letri
  let cA: class A
  let cB: class B
  let cC: class C
  assume lt.1: |- A e. RR
  assume lt.2: |- B e. RR
  assume lt.3: |- C e. RR


  assert |- ( ( A <_ B /\ B <_ C ) -> A <_ C )

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
    cA
    cB
    cle
    wbr
    cB
    cC
    cle
    wbr
    wa
    cA
    cC
    cle
    wbr
    wi
    lt.1
    lt.2
    lt.3
    cA
    cB
    cC
    letr
    mp3an
end
