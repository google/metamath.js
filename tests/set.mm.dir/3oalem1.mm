include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cva.mm"
include "co.mm"
include "wceq.mm"
include "chil.mm"
include "cheli.mm"
include "anim12i.mm"
include "hvaddcl.mm"
include "eleq1.mm"
include "syl5ibrcom.mm"
include "imdistani.mm"
include "sylan.mm"
include "adantr.mm"

theorem 3oalem1
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  let cB: class B
  let cC: class C
  let cR: class R
  let cS: class S
  assume 3oalem1.1: |- B e. CH
  assume 3oalem1.2: |- C e. CH
  assume 3oalem1.3: |- R e. CH
  assume 3oalem1.4: |- S e. CH

  disjoint x y
  disjoint x z
  disjoint w x
  disjoint v x
  disjoint B x
  disjoint y z
  disjoint w y
  disjoint v y
  disjoint B y
  disjoint w z
  disjoint v z
  disjoint B z
  disjoint v w
  disjoint B w
  disjoint B v
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint C w
  disjoint C v
  disjoint R x
  disjoint R y
  disjoint R z
  disjoint R w
  disjoint R v
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint S w
  disjoint S v
  assert |- ( ( ( ( x e. B /\ y e. R ) /\ v = ( x +h y ) ) /\ ( ( z e. C /\ w e. S ) /\ v = ( z +h w ) ) ) -> ( ( ( x e. ~H /\ y e. ~H ) /\ v e. ~H ) /\ ( z e. ~H /\ w e. ~H ) ) )

  proof
    vx
    cv
    #
    cB
    wcel
    #
    vy
    cv
    #
    cR
    wcel
    #
    wa
    #
    vv
    cv
    #
    @0
    @2
    cva
    co
    #
    wceq
    #
    wa
    @0
    chil
    wcel
    #
    @2
    chil
    wcel
    #
    wa
    #
    @5
    chil
    wcel
    #
    wa
    #
    vz
    cv
    #
    cC
    wcel
    #
    vw
    cv
    #
    cS
    wcel
    #
    wa
    #
    @5
    @13
    @15
    cva
    co
    wceq
    #
    wa
    @13
    chil
    wcel
    #
    @15
    chil
    wcel
    #
    wa
    #
    @4
    @10
    @7
    @12
    @1
    @8
    @3
    @9
    @0
    cB
    3oalem1.1
    cheli
    @2
    cR
    3oalem1.3
    cheli
    anim12i
    @10
    @7
    @11
    @10
    @11
    @7
    @6
    chil
    wcel
    @0
    @2
    hvaddcl
    @5
    @6
    chil
    eleq1
    syl5ibrcom
    imdistani
    sylan
    @17
    @21
    @18
    @14
    @19
    @16
    @20
    @13
    cC
    3oalem1.2
    cheli
    @15
    cS
    3oalem1.4
    cheli
    anim12i
    adantr
    anim12i
end
