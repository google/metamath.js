include "cr.mm"
include "wcel.mm"
include "cicc.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "w3a.mm"
include "wb.mm"
include "elicc2.mm"
include "mp2an.mm"

theorem elicc2i
  let cA: class A
  let cB: class B
  let cC: class C
  assume elicc2i.1: |- A e. RR
  assume elicc2i.2: |- B e. RR


  assert |- ( C e. ( A [,] B ) <-> ( C e. RR /\ A <_ C /\ C <_ B ) )

  proof
    cA
    cr
    wcel
    cB
    cr
    wcel
    cC
    cA
    cB
    cicc
    co
    wcel
    cC
    cr
    wcel
    cA
    cC
    cle
    wbr
    cC
    cB
    cle
    wbr
    w3a
    wb
    elicc2i.1
    elicc2i.2
    cA
    cB
    cC
    elicc2
    mp2an
end
