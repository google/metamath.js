include "cv.mm"
include "cop.mm"
include "cec.mm"
include "co.mm"
include "wceq.mm"
include "oveq1.mm"
include "oveq2.mm"
include "eqeq12d.mm"
include "wcel.mm"
include "wa.mm"
include "opeq12.mm"
include "eceq1d.mm"
include "mp2an.mm"
include "ancoms.mm"
include "3eqtr4a.mm"
include "2ecoptocl.mm"

theorem ecovcom
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let c.pl: class .+
  let c.sm: class .~
  let cS: class S
  let cG: class G
  let cH: class H
  let cJ: class J
  assume ecovcom.1: |- C = ( ( S X. S ) /. .~ )
  assume ecovcom.2: |- ( ( ( x e. S /\ y e. S ) /\ ( z e. S /\ w e. S ) ) -> ( [ <. x , y >. ] .~ .+ [ <. z , w >. ] .~ ) = [ <. D , G >. ] .~ )
  assume ecovcom.3: |- ( ( ( z e. S /\ w e. S ) /\ ( x e. S /\ y e. S ) ) -> ( [ <. z , w >. ] .~ .+ [ <. x , y >. ] .~ ) = [ <. H , J >. ] .~ )
  assume ecovcom.4: |- D = H
  assume ecovcom.5: |- G = J

  disjoint x y
  disjoint x z
  disjoint w x
  disjoint A x
  disjoint y z
  disjoint w y
  disjoint A y
  disjoint w z
  disjoint A z
  disjoint A w
  disjoint B z
  disjoint B w
  disjoint .+ x
  disjoint .+ y
  disjoint .+ z
  disjoint .+ w
  disjoint .~ x
  disjoint .~ y
  disjoint .~ z
  disjoint .~ w
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint S w
  disjoint C z
  disjoint C w
  assert |- ( ( A e. C /\ B e. C ) -> ( A .+ B ) = ( B .+ A ) )

  proof
    vx
    cv
    #
    vy
    cv
    #
    cop
    c.sm
    cec
    #
    vz
    cv
    #
    vw
    cv
    #
    cop
    c.sm
    cec
    #
    c.pl
    co
    #
    @5
    @2
    c.pl
    co
    #
    wceq
    cA
    @5
    c.pl
    co
    #
    @5
    cA
    c.pl
    co
    #
    wceq
    cA
    cB
    c.pl
    co
    #
    cB
    cA
    c.pl
    co
    #
    wceq
    vx
    vy
    vz
    vw
    cA
    cB
    cS
    cS
    c.sm
    cC
    ecovcom.1
    @2
    cA
    wceq
    @6
    @8
    @7
    @9
    @2
    cA
    @5
    c.pl
    oveq1
    @2
    cA
    @5
    c.pl
    oveq2
    eqeq12d
    @5
    cB
    wceq
    @8
    @10
    @9
    @11
    @5
    cB
    cA
    c.pl
    oveq2
    @5
    cB
    cA
    c.pl
    oveq1
    eqeq12d
    @0
    cS
    wcel
    @1
    cS
    wcel
    wa
    #
    @3
    cS
    wcel
    @4
    cS
    wcel
    wa
    #
    wa
    cD
    cG
    cop
    #
    c.sm
    cec
    #
    cH
    cJ
    cop
    #
    c.sm
    cec
    #
    @6
    @7
    cD
    cH
    wceq
    #
    cG
    cJ
    wceq
    #
    @15
    @17
    wceq
    ecovcom.4
    ecovcom.5
    @18
    @19
    wa
    @14
    @16
    c.sm
    cD
    cG
    cH
    cJ
    opeq12
    eceq1d
    mp2an
    ecovcom.2
    @13
    @12
    @7
    @17
    wceq
    ecovcom.3
    ancoms
    3eqtr4a
    2ecoptocl
end
