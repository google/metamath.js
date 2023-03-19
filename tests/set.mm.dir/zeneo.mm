include "c2.mm"
include "cdvds.mm"
include "wbr.mm"
include "wn.mm"
include "wa.mm"
include "wne.mm"
include "wi.mm"
include "cz.mm"
include "wcel.mm"
include "nbrne1.mm"
include "a1i.mm"

theorem zeneo
  let cA: class A
  let cB: class B


  assert |- ( ( A e. ZZ /\ B e. ZZ ) -> ( ( 2 || A /\ -. 2 || B ) -> A =/= B ) )

  proof
    c2
    cA
    cdvds
    wbr
    c2
    cB
    cdvds
    wbr
    wn
    wa
    cA
    cB
    wne
    wi
    cA
    cz
    wcel
    cB
    cz
    wcel
    wa
    c2
    cA
    cB
    cdvds
    nbrne1
    a1i
end
