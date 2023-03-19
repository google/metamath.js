include "co.mm"
include "wbr.mm"
include "cvv.mm"
include "wcel.mm"
include "wa.mm"
include "cop.mm"
include "wi.mm"
include "df-br.mm"
include "c0.mm"
include "wne.mm"
include "ne0i.mm"
include "mpt2ndm0.mm"
include "necon1ai.mm"
include "wrel.mm"
include "brrelex12.mm"
include "sylan.mm"
include "id.mm"
include "syldan.mm"
include "ex.mm"
include "3syl.mm"
include "sylbi.mm"
include "pm2.43i.mm"

theorem brovex
  let vx: setvar x
  let vy: setvar y
  let cC: class C
  let cP: class P
  let cE: class E
  let cF: class F
  let cO: class O
  let cV: class V
  assume brovex.1: |- O = ( x e. _V , y e. _V |-> C )
  assume brovex.2: |- ( ( V e. _V /\ E e. _V ) -> Rel ( V O E ) )

  disjoint x y
  assert |- ( F ( V O E ) P -> ( ( V e. _V /\ E e. _V ) /\ ( F e. _V /\ P e. _V ) ) )

  proof
    cF
    cP
    cV
    cE
    cO
    co
    #
    wbr
    #
    cV
    cvv
    wcel
    cE
    cvv
    wcel
    wa
    #
    cF
    cvv
    wcel
    cP
    cvv
    wcel
    wa
    #
    wa
    #
    @1
    cF
    cP
    cop
    #
    @0
    wcel
    #
    @1
    @4
    wi
    #
    cF
    cP
    @0
    df-br
    @6
    @0
    c0
    wne
    @2
    @7
    @0
    @5
    ne0i
    @2
    @0
    c0
    vx
    vy
    cC
    cO
    cV
    cE
    cvv
    cvv
    brovex.1
    mpt2ndm0
    necon1ai
    @2
    @1
    @4
    @2
    @1
    @3
    @4
    @2
    @0
    wrel
    @1
    @3
    brovex.2
    cF
    cP
    @0
    brrelex12
    sylan
    @4
    id
    syldan
    ex
    3syl
    sylbi
    pm2.43i
end
