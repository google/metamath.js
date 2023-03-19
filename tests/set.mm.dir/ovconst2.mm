include "wcel.mm"
include "wa.mm"
include "cxp.mm"
include "csn.mm"
include "co.mm"
include "cop.mm"
include "cfv.mm"
include "df-ov.mm"
include "wceq.mm"
include "opelxpi.mm"
include "fvconst2.mm"
include "syl.mm"
include "syl5eq.mm"

theorem ovconst2
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let cS: class S
  assume oprvalconst2.1: |- C e. _V


  assert |- ( ( R e. A /\ S e. B ) -> ( R ( ( A X. B ) X. { C } ) S ) = C )

  proof
    cR
    cA
    wcel
    cS
    cB
    wcel
    wa
    #
    cR
    cS
    cA
    cB
    cxp
    #
    cC
    csn
    cxp
    #
    co
    cR
    cS
    cop
    #
    @2
    cfv
    #
    cC
    cR
    cS
    @2
    df-ov
    @0
    @3
    @1
    wcel
    @4
    cC
    wceq
    cR
    cS
    cA
    cB
    opelxpi
    @1
    cC
    @3
    oprvalconst2.1
    fvconst2
    syl
    syl5eq
end
