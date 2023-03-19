include "cv.mm"
include "cop.mm"
include "cec.mm"
include "co.mm"
include "wceq.mm"
include "oveq1.mm"
include "oveq1d.mm"
include "eqeq12d.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "wcel.mm"
include "wa.mm"
include "w3a.mm"
include "opeq12.mm"
include "eceq1d.mm"
include "mp2an.mm"
include "adantr.mm"
include "sylan.mm"
include "eqtrd.mm"
include "3impa.mm"
include "adantl.mm"
include "sylan2.mm"
include "3impb.mm"
include "3eqtr4a.mm"
include "3ecoptocl.mm"

theorem ecovass
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  let vu: setvar u
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let c.pl: class .+
  let cQ: class Q
  let c.sm: class .~
  let cS: class S
  let cG: class G
  let cH: class H
  let cJ: class J
  let cK: class K
  let cL: class L
  let cM: class M
  let cN: class N
  assume ecovass.1: |- D = ( ( S X. S ) /. .~ )
  assume ecovass.2: |- ( ( ( x e. S /\ y e. S ) /\ ( z e. S /\ w e. S ) ) -> ( [ <. x , y >. ] .~ .+ [ <. z , w >. ] .~ ) = [ <. G , H >. ] .~ )
  assume ecovass.3: |- ( ( ( z e. S /\ w e. S ) /\ ( v e. S /\ u e. S ) ) -> ( [ <. z , w >. ] .~ .+ [ <. v , u >. ] .~ ) = [ <. N , Q >. ] .~ )
  assume ecovass.4: |- ( ( ( G e. S /\ H e. S ) /\ ( v e. S /\ u e. S ) ) -> ( [ <. G , H >. ] .~ .+ [ <. v , u >. ] .~ ) = [ <. J , K >. ] .~ )
  assume ecovass.5: |- ( ( ( x e. S /\ y e. S ) /\ ( N e. S /\ Q e. S ) ) -> ( [ <. x , y >. ] .~ .+ [ <. N , Q >. ] .~ ) = [ <. L , M >. ] .~ )
  assume ecovass.6: |- ( ( ( x e. S /\ y e. S ) /\ ( z e. S /\ w e. S ) ) -> ( G e. S /\ H e. S ) )
  assume ecovass.7: |- ( ( ( z e. S /\ w e. S ) /\ ( v e. S /\ u e. S ) ) -> ( N e. S /\ Q e. S ) )
  assume ecovass.8: |- J = L
  assume ecovass.9: |- K = M

  disjoint x y
  disjoint x z
  disjoint w x
  disjoint v x
  disjoint u x
  disjoint A x
  disjoint y z
  disjoint w y
  disjoint v y
  disjoint u y
  disjoint A y
  disjoint w z
  disjoint v z
  disjoint u z
  disjoint A z
  disjoint v w
  disjoint u w
  disjoint A w
  disjoint u v
  disjoint A v
  disjoint A u
  disjoint B z
  disjoint B w
  disjoint B v
  disjoint B u
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint C w
  disjoint C v
  disjoint C u
  disjoint .+ x
  disjoint .+ y
  disjoint .+ z
  disjoint .+ w
  disjoint .+ v
  disjoint .+ u
  disjoint .~ x
  disjoint .~ y
  disjoint .~ z
  disjoint .~ w
  disjoint .~ v
  disjoint .~ u
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint S w
  disjoint S v
  disjoint S u
  disjoint D z
  disjoint D w
  disjoint D v
  disjoint D u
  assert |- ( ( A e. D /\ B e. D /\ C e. D ) -> ( ( A .+ B ) .+ C ) = ( A .+ ( B .+ C ) ) )

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
    vv
    cv
    #
    vu
    cv
    #
    cop
    c.sm
    cec
    #
    c.pl
    co
    #
    @2
    @5
    @9
    c.pl
    co
    #
    c.pl
    co
    #
    wceq
    cA
    @5
    c.pl
    co
    #
    @9
    c.pl
    co
    #
    cA
    @11
    c.pl
    co
    #
    wceq
    cA
    cB
    c.pl
    co
    #
    @9
    c.pl
    co
    #
    cA
    cB
    @9
    c.pl
    co
    #
    c.pl
    co
    #
    wceq
    @16
    cC
    c.pl
    co
    #
    cA
    cB
    cC
    c.pl
    co
    #
    c.pl
    co
    #
    wceq
    vx
    vy
    vz
    vw
    vv
    vu
    cA
    cB
    cC
    cS
    c.sm
    cD
    ecovass.1
    @2
    cA
    wceq
    #
    @10
    @14
    @12
    @15
    @23
    @6
    @13
    @9
    c.pl
    @2
    cA
    @5
    c.pl
    oveq1
    oveq1d
    @2
    cA
    @11
    c.pl
    oveq1
    eqeq12d
    @5
    cB
    wceq
    #
    @14
    @17
    @15
    @19
    @24
    @13
    @16
    @9
    c.pl
    @5
    cB
    cA
    c.pl
    oveq2
    oveq1d
    @24
    @11
    @18
    cA
    c.pl
    @5
    cB
    @9
    c.pl
    oveq1
    oveq2d
    eqeq12d
    @9
    cC
    wceq
    #
    @17
    @20
    @19
    @22
    @9
    cC
    @16
    c.pl
    oveq2
    @25
    @18
    @21
    cA
    c.pl
    @9
    cC
    cB
    c.pl
    oveq2
    oveq2d
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
    @7
    cS
    wcel
    @8
    cS
    wcel
    wa
    #
    w3a
    cJ
    cK
    cop
    #
    c.sm
    cec
    #
    cL
    cM
    cop
    #
    c.sm
    cec
    #
    @10
    @12
    cJ
    cL
    wceq
    #
    cK
    cM
    wceq
    #
    @30
    @32
    wceq
    ecovass.8
    ecovass.9
    @33
    @34
    wa
    @29
    @31
    c.sm
    cJ
    cK
    cL
    cM
    opeq12
    eceq1d
    mp2an
    @26
    @27
    @28
    @10
    @30
    wceq
    @26
    @27
    wa
    #
    @28
    wa
    @10
    cG
    cH
    cop
    c.sm
    cec
    #
    @9
    c.pl
    co
    #
    @30
    @35
    @10
    @37
    wceq
    @28
    @35
    @6
    @36
    @9
    c.pl
    ecovass.2
    oveq1d
    adantr
    @35
    cG
    cS
    wcel
    cH
    cS
    wcel
    wa
    @28
    @37
    @30
    wceq
    ecovass.6
    ecovass.4
    sylan
    eqtrd
    3impa
    @26
    @27
    @28
    @12
    @32
    wceq
    @26
    @27
    @28
    wa
    #
    wa
    @12
    @2
    cN
    cQ
    cop
    c.sm
    cec
    #
    c.pl
    co
    #
    @32
    @38
    @12
    @40
    wceq
    @26
    @38
    @11
    @39
    @2
    c.pl
    ecovass.3
    oveq2d
    adantl
    @38
    @26
    cN
    cS
    wcel
    cQ
    cS
    wcel
    wa
    @40
    @32
    wceq
    ecovass.7
    ecovass.5
    sylan2
    eqtrd
    3impb
    3eqtr4a
    3ecoptocl
end
