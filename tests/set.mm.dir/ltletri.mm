include "cr.mm"
include "wcel.mm"
include "clt.mm"
include "wbr.mm"
include "cle.mm"
include "wa.mm"
include "wi.mm"
include "ltletr.mm"
include "mp3an.mm"

theorem ltletri
  let cA: class A
  let cB: class B
  let cC: class C
  assume lt.1: |- A e. RR
  assume lt.2: |- B e. RR
  assume lt.3: |- C e. RR


  assert |- ( ( A < B /\ B <_ C ) -> A < C )

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
    clt
    wbr
    cB
    cC
    cle
    wbr
    wa
    cA
    cC
    clt
    wbr
    wi
    lt.1
    lt.2
    lt.3
    cA
    cB
    cC
    ltletr
    mp3an
end
