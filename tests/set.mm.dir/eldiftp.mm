include "ctp.mm"
include "cdif.mm"
include "wcel.mm"
include "wn.mm"
include "wa.mm"
include "wne.mm"
include "w3a.mm"
include "eldif.mm"
include "wceq.mm"
include "w3o.mm"
include "eltpg.mm"
include "notbid.mm"
include "ne3anior.mm"
include "syl6bbr.mm"
include "pm5.32i.mm"
include "bitri.mm"

theorem eldiftp
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E


  assert |- ( A e. ( B \ { C , D , E } ) <-> ( A e. B /\ ( A =/= C /\ A =/= D /\ A =/= E ) ) )

  proof
    cA
    cB
    cC
    cD
    cE
    ctp
    #
    cdif
    wcel
    cA
    cB
    wcel
    #
    cA
    @0
    wcel
    #
    wn
    #
    wa
    @1
    cA
    cC
    wne
    cA
    cD
    wne
    cA
    cE
    wne
    w3a
    #
    wa
    cA
    cB
    @0
    eldif
    @1
    @3
    @4
    @1
    @3
    cA
    cC
    wceq
    cA
    cD
    wceq
    cA
    cE
    wceq
    w3o
    #
    wn
    @4
    @1
    @2
    @5
    cA
    cC
    cD
    cE
    cB
    eltpg
    notbid
    cA
    cC
    cA
    cD
    cA
    cE
    ne3anior
    syl6bbr
    pm5.32i
    bitri
end
