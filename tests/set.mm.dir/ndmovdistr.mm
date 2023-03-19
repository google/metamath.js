include "wcel.mm"
include "w3a.mm"
include "wn.mm"
include "co.mm"
include "c0.mm"
include "wa.mm"
include "wceq.mm"
include "ndmovrcl.mm"
include "anim2i.mm"
include "3anass.mm"
include "sylibr.mm"
include "con3i.mm"
include "ndmov.mm"
include "syl.mm"
include "anim12i.mm"
include "anandi3.mm"
include "eqtr4d.mm"

theorem ndmovdistr
  let cA: class A
  let cB: class B
  let cC: class C
  let cS: class S
  let cF: class F
  let cG: class G
  assume ndmov.1: |- dom F = ( S X. S )
  assume ndmov.5: |- -. (/) e. S
  assume ndmov.6: |- dom G = ( S X. S )


  assert |- ( -. ( A e. S /\ B e. S /\ C e. S ) -> ( A G ( B F C ) ) = ( ( A G B ) F ( A G C ) ) )

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
    cC
    cF
    co
    #
    cG
    co
    #
    c0
    cA
    cB
    cG
    co
    #
    cA
    cC
    cG
    co
    #
    cF
    co
    #
    @4
    @0
    @5
    cS
    wcel
    #
    wa
    #
    wn
    @6
    c0
    wceq
    @11
    @3
    @11
    @0
    @1
    @2
    wa
    #
    wa
    @3
    @10
    @12
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
    @5
    cS
    cG
    ndmov.6
    ndmov
    syl
    @4
    @7
    cS
    wcel
    #
    @8
    cS
    wcel
    #
    wa
    #
    wn
    @9
    c0
    wceq
    @15
    @3
    @15
    @0
    @1
    wa
    #
    @0
    @2
    wa
    #
    wa
    @3
    @13
    @16
    @14
    @17
    cA
    cB
    cS
    cG
    ndmov.6
    ndmov.5
    ndmovrcl
    cA
    cC
    cS
    cG
    ndmov.6
    ndmov.5
    ndmovrcl
    anim12i
    @0
    @1
    @2
    anandi3
    sylibr
    con3i
    @7
    @8
    cS
    cF
    ndmov.1
    ndmov
    syl
    eqtr4d
end
