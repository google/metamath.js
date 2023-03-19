include "cablo.mm"
include "wcel.mm"
include "wa.mm"
include "co.mm"
include "wceq.mm"
include "w3a.mm"
include "df-3an.mm"
include "ablomuldiv.mm"
include "sylan2br.mm"
include "adantrrr.mm"
include "oveq1d.mm"
include "cgr.mm"
include "wi.mm"
include "ablogrpo.mm"
include "grpocl.mm"
include "3expib.mm"
include "syl.mm"
include "anim1d.mm"
include "3anass.mm"
include "syl6ibr.mm"
include "imp.mm"
include "ablodivdiv4.mm"
include "syldan.mm"
include "grpodivcl.mm"
include "an4.mm"
include "3imtr4g.mm"
include "grpomuldivass.mm"
include "sylan.mm"
include "3eqtr3d.mm"

theorem ablo4pnp
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cF: class F
  let cG: class G
  let cX: class X
  assume abl4pnp.1: |- X = ran G
  assume abl4pnp.2: |- D = ( /g ` G )


  assert |- ( ( G e. AbelOp /\ ( ( A e. X /\ B e. X ) /\ ( C e. X /\ F e. X ) ) ) -> ( ( A G B ) D ( C G F ) ) = ( ( A D C ) G ( B D F ) ) )

  proof
    cG
    cablo
    wcel
    #
    cA
    cX
    wcel
    #
    cB
    cX
    wcel
    #
    wa
    #
    cC
    cX
    wcel
    #
    cF
    cX
    wcel
    #
    wa
    #
    wa
    #
    wa
    #
    cA
    cB
    cG
    co
    #
    cC
    cD
    co
    #
    cF
    cD
    co
    #
    cA
    cC
    cD
    co
    #
    cB
    cG
    co
    #
    cF
    cD
    co
    #
    @9
    cC
    cF
    cG
    co
    cD
    co
    #
    @12
    cB
    cF
    cD
    co
    cG
    co
    #
    @8
    @10
    @13
    cF
    cD
    @0
    @3
    @4
    @10
    @13
    wceq
    #
    @5
    @3
    @4
    wa
    @0
    @1
    @2
    @4
    w3a
    @17
    @1
    @2
    @4
    df-3an
    cA
    cB
    cC
    cD
    cG
    cX
    abl4pnp.1
    abl4pnp.2
    ablomuldiv
    sylan2br
    adantrrr
    oveq1d
    @0
    @7
    @9
    cX
    wcel
    #
    @4
    @5
    w3a
    #
    @11
    @15
    wceq
    @0
    @7
    @19
    @0
    @7
    @18
    @6
    wa
    @19
    @0
    @3
    @18
    @6
    @0
    cG
    cgr
    wcel
    #
    @3
    @18
    wi
    cG
    ablogrpo
    #
    @20
    @1
    @2
    @18
    cA
    cB
    cG
    cX
    abl4pnp.1
    grpocl
    3expib
    syl
    anim1d
    @18
    @4
    @5
    3anass
    syl6ibr
    imp
    @9
    cC
    cF
    cD
    cG
    cX
    abl4pnp.1
    abl4pnp.2
    ablodivdiv4
    syldan
    @0
    @20
    @7
    @14
    @16
    wceq
    #
    @21
    @20
    @7
    @12
    cX
    wcel
    #
    @2
    @5
    w3a
    #
    @22
    @20
    @7
    @24
    @20
    @1
    @4
    wa
    #
    @2
    @5
    wa
    #
    wa
    @23
    @26
    wa
    @7
    @24
    @20
    @25
    @23
    @26
    @20
    @1
    @4
    @23
    cA
    cC
    cD
    cG
    cX
    abl4pnp.1
    abl4pnp.2
    grpodivcl
    3expib
    anim1d
    @1
    @2
    @4
    @5
    an4
    @23
    @2
    @5
    3anass
    3imtr4g
    imp
    @12
    cB
    cF
    cD
    cG
    cX
    abl4pnp.1
    abl4pnp.2
    grpomuldivass
    syldan
    sylan
    3eqtr3d
end
