include "wpo.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "po2nr.mm"
include "3adantr2.mm"
include "df-3an.mm"
include "potr.mm"
include "anim1d.mm"
include "syl5bi.mm"
include "mtod.mm"

theorem po3nr
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R


  assert |- ( ( R Po A /\ ( B e. A /\ C e. A /\ D e. A ) ) -> -. ( B R C /\ C R D /\ D R B ) )

  proof
    cA
    cR
    wpo
    #
    cB
    cA
    wcel
    #
    cC
    cA
    wcel
    #
    cD
    cA
    wcel
    #
    w3a
    wa
    #
    cB
    cC
    cR
    wbr
    #
    cC
    cD
    cR
    wbr
    #
    cD
    cB
    cR
    wbr
    #
    w3a
    #
    cB
    cD
    cR
    wbr
    #
    @7
    wa
    #
    @0
    @1
    @3
    @10
    wn
    @2
    cA
    cB
    cD
    cR
    po2nr
    3adantr2
    @8
    @5
    @6
    wa
    #
    @7
    wa
    @4
    @10
    @5
    @6
    @7
    df-3an
    @4
    @11
    @9
    @7
    cA
    cB
    cC
    cD
    cR
    potr
    anim1d
    syl5bi
    mtod
end
