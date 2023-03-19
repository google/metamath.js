include "wcel.mm"
include "word.mm"
include "wa.mm"
include "csuc.mm"
include "wss.mm"
include "wi.mm"
include "ordsucss.mm"
include "adantl.mm"
include "sucssel.mm"
include "adantr.mm"
include "impbid.mm"

theorem ordelsuc
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. C /\ Ord B ) -> ( A e. B <-> suc A C_ B ) )

  proof
    cA
    cC
    wcel
    #
    cB
    word
    #
    wa
    cA
    cB
    wcel
    #
    cA
    csuc
    cB
    wss
    #
    @1
    @2
    @3
    wi
    @0
    cA
    cB
    ordsucss
    adantl
    @0
    @3
    @2
    wi
    @1
    cA
    cB
    cC
    sucssel
    adantr
    impbid
end
