include "wcel.mm"
include "w3a.mm"
include "wn.mm"
include "co.mm"
include "c0.mm"
include "wa.mm"
include "wceq.mm"
include "ndmovrcl.mm"
include "anim1i.mm"
include "df-3an.mm"
include "sylibr.mm"
include "con3i.mm"
include "ndmov.mm"
include "syl.mm"
include "anim2i.mm"
include "3anass.mm"
include "eqtr4d.mm"

theorem ndmovass
  let cA: class A
  let cB: class B
  let cC: class C
  let cS: class S
  let cF: class F
  assume ndmov.1: |- dom F = ( S X. S )
  assume ndmov.5: |- -. (/) e. S


  assert |- ( -. ( A e. S /\ B e. S /\ C e. S ) -> ( ( A F B ) F C ) = ( A F ( B F C ) ) )

  proof
    cA
    cS
    wcel
    #
    cB
    cS
    wcel
    #
    cC
    cS
    wcel
    #
    w3a
    #
    wn
    #
    cA
    cB
    cF
    co
    #
    cC
    cF
    co
    #
    c0
    cA
    cB
    cC
    cF
    co
    #
    cF
    co
    #
    @4
    @5
    cS
    wcel
    #
    @2
    wa
    #
    wn
    @6
    c0
    wceq
    @10
    @3
    @10
    @0
    @1
    wa
    #
    @2
    wa
    @3
    @9
    @11
    @2
    cA
    cB
    cS
    cF
    ndmov.1
    ndmov.5
    ndmovrcl
    anim1i
    @0
    @1
    @2
    df-3an
    sylibr
    con3i
    @5
    cC
    cS
    cF
    ndmov.1
    ndmov
    syl
    @4
    @0
    @7
    cS
    wcel
    #
    wa
    #
    wn
    @8
    c0
    wceq
    @13
    @3
    @13
    @0
    @1
    @2
    wa
    #
    wa
    @3
    @12
    @14
    @0
    cB
    cC
    cS
    cF
    ndmov.1
    ndmov.5
    ndmovrcl
    anim2i
    @0
    @1
    @2
    3anass
    sylibr
    con3i
    cA
    @7
    cS
    cF
    ndmov.1
    ndmov
    syl
    eqtr4d
end
