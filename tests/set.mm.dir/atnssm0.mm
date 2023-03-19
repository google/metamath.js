include "cch.mm"
include "wcel.mm"
include "cat.mm"
include "wa.mm"
include "wss.mm"
include "wn.mm"
include "chj.mm"
include "co.mm"
include "ccv.mm"
include "wbr.mm"
include "cin.mm"
include "c0h.mm"
include "wceq.mm"
include "chcv1.mm"
include "cvp.mm"
include "bitr4d.mm"

theorem atnssm0
  let cA: class A
  let cB: class B


  assert |- ( ( A e. CH /\ B e. HAtoms ) -> ( -. B C_ A <-> ( A i^i B ) = 0H ) )

  proof
    cA
    cch
    wcel
    cB
    cat
    wcel
    wa
    cB
    cA
    wss
    wn
    cA
    cA
    cB
    chj
    co
    ccv
    wbr
    cA
    cB
    cin
    c0h
    wceq
    cA
    cB
    chcv1
    cA
    cB
    cvp
    bitr4d
end
