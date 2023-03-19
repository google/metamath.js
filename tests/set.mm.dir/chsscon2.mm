include "cch.mm"
include "wcel.mm"
include "chil.mm"
include "wss.mm"
include "cort.mm"
include "cfv.mm"
include "wb.mm"
include "chss.mm"
include "occon3.mm"
include "syl2an.mm"

theorem chsscon2
  let cA: class A
  let cB: class B


  assert |- ( ( A e. CH /\ B e. CH ) -> ( A C_ ( _|_ ` B ) <-> B C_ ( _|_ ` A ) ) )

  proof
    cA
    cch
    wcel
    cA
    chil
    wss
    cB
    chil
    wss
    cA
    cB
    cort
    cfv
    wss
    cB
    cA
    cort
    cfv
    wss
    wb
    cB
    cch
    wcel
    cA
    chss
    cB
    chss
    cA
    cB
    occon3
    syl2an
end
