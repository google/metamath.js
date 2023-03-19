include "cv.mm"
include "cop.mm"
include "cec.mm"
include "co.mm"
include "wceq.mm"
include "oveq1.mm"
include "oveq12d.mm"
include "eqeq12d.mm"
include "oveq2d.mm"
include "oveq2.mm"
include "oveq1d.mm"
include "wcel.mm"
include "wa.mm"
include "w3a.mm"
include "opeq12.mm"
include "eceq1d.mm"
include "mp2an.mm"
include "adantl.mm"
include "sylan2.mm"
include "eqtrd.mm"
include "3impb.mm"
include "oveqan12d.mm"
include "syl2an.mm"
include "3impdi.mm"
include "3eqtr4a.mm"
include "3ecoptocl.mm"

theorem ecovdi
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
  let c.sm: class .~
  let cS: class S
  let c.x: class .x.
  let cH: class H
  let cJ: class J
  let cK: class K
  let cL: class L
  let cM: class M
  let cN: class N
  let cW: class W
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume ecovdi.1: |- D = ( ( S X. S ) /. .~ )
  assume ecovdi.2: |- ( ( ( z e. S /\ w e. S ) /\ ( v e. S /\ u e. S ) ) -> ( [ <. z , w >. ] .~ .+ [ <. v , u >. ] .~ ) = [ <. M , N >. ] .~ )
  assume ecovdi.3: |- ( ( ( x e. S /\ y e. S ) /\ ( M e. S /\ N e. S ) ) -> ( [ <. x , y >. ] .~ .x. [ <. M , N >. ] .~ ) = [ <. H , J >. ] .~ )
  assume ecovdi.4: |- ( ( ( x e. S /\ y e. S ) /\ ( z e. S /\ w e. S ) ) -> ( [ <. x , y >. ] .~ .x. [ <. z , w >. ] .~ ) = [ <. W , X >. ] .~ )
  assume ecovdi.5: |- ( ( ( x e. S /\ y e. S ) /\ ( v e. S /\ u e. S ) ) -> ( [ <. x , y >. ] .~ .x. [ <. v , u >. ] .~ ) = [ <. Y , Z >. ] .~ )
  assume ecovdi.6: |- ( ( ( W e. S /\ X e. S ) /\ ( Y e. S /\ Z e. S ) ) -> ( [ <. W , X >. ] .~ .+ [ <. Y , Z >. ] .~ ) = [ <. K , L >. ] .~ )
  assume ecovdi.7: |- ( ( ( z e. S /\ w e. S ) /\ ( v e. S /\ u e. S ) ) -> ( M e. S /\ N e. S ) )
  assume ecovdi.8: |- ( ( ( x e. S /\ y e. S ) /\ ( z e. S /\ w e. S ) ) -> ( W e. S /\ X e. S ) )
  assume ecovdi.9: |- ( ( ( x e. S /\ y e. S ) /\ ( v e. S /\ u e. S ) ) -> ( Y e. S /\ Z e. S ) )
  assume ecovdi.10: |- H = K
  assume ecovdi.11: |- J = L

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
  disjoint .x. x
  disjoint .x. y
  disjoint .x. z
  disjoint .x. w
  disjoint .x. v
  disjoint .x. u
  disjoint D z
  disjoint D w
  disjoint D v
  disjoint D u
  assert |- ( ( A e. D /\ B e. D /\ C e. D ) -> ( A .x. ( B .+ C ) ) = ( ( A .x. B ) .+ ( A .x. C ) ) )

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
    c.x
    co
    #
    @2
    @5
    c.x
    co
    #
    @2
    @8
    c.x
    co
    #
    c.pl
    co
    #
    wceq
    cA
    @9
    c.x
    co
    #
    cA
    @5
    c.x
    co
    #
    cA
    @8
    c.x
    co
    #
    c.pl
    co
    #
    wceq
    cA
    cB
    @8
    c.pl
    co
    #
    c.x
    co
    #
    cA
    cB
    c.x
    co
    #
    @16
    c.pl
    co
    #
    wceq
    cA
    cB
    cC
    c.pl
    co
    #
    c.x
    co
    #
    @20
    cA
    cC
    c.x
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
    ecovdi.1
    @2
    cA
    wceq
    #
    @10
    @14
    @13
    @17
    @2
    cA
    @9
    c.x
    oveq1
    @26
    @11
    @15
    @12
    @16
    c.pl
    @2
    cA
    @5
    c.x
    oveq1
    @2
    cA
    @8
    c.x
    oveq1
    oveq12d
    eqeq12d
    @5
    cB
    wceq
    #
    @14
    @19
    @17
    @21
    @27
    @9
    @18
    cA
    c.x
    @5
    cB
    @8
    c.pl
    oveq1
    oveq2d
    @27
    @15
    @20
    @16
    c.pl
    @5
    cB
    cA
    c.x
    oveq2
    oveq1d
    eqeq12d
    @8
    cC
    wceq
    #
    @19
    @23
    @21
    @25
    @28
    @18
    @22
    cA
    c.x
    @8
    cC
    cB
    c.pl
    oveq2
    oveq2d
    @28
    @16
    @24
    @20
    c.pl
    @8
    cC
    cA
    c.x
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
    @6
    cS
    wcel
    @7
    cS
    wcel
    wa
    #
    w3a
    cH
    cJ
    cop
    #
    c.sm
    cec
    #
    cK
    cL
    cop
    #
    c.sm
    cec
    #
    @10
    @13
    cH
    cK
    wceq
    #
    cJ
    cL
    wceq
    #
    @33
    @35
    wceq
    ecovdi.10
    ecovdi.11
    @36
    @37
    wa
    @32
    @34
    c.sm
    cH
    cJ
    cK
    cL
    opeq12
    eceq1d
    mp2an
    @29
    @30
    @31
    @10
    @33
    wceq
    @29
    @30
    @31
    wa
    #
    wa
    @10
    @2
    cM
    cN
    cop
    c.sm
    cec
    #
    c.x
    co
    #
    @33
    @38
    @10
    @40
    wceq
    @29
    @38
    @9
    @39
    @2
    c.x
    ecovdi.2
    oveq2d
    adantl
    @38
    @29
    cM
    cS
    wcel
    cN
    cS
    wcel
    wa
    @40
    @33
    wceq
    ecovdi.7
    ecovdi.3
    sylan2
    eqtrd
    3impb
    @29
    @30
    @31
    @13
    @35
    wceq
    @29
    @30
    wa
    #
    @29
    @31
    wa
    #
    wa
    @13
    cW
    cX
    cop
    c.sm
    cec
    #
    cY
    cZ
    cop
    c.sm
    cec
    #
    c.pl
    co
    #
    @35
    @41
    @42
    @11
    @43
    @12
    @44
    c.pl
    ecovdi.4
    ecovdi.5
    oveqan12d
    @41
    cW
    cS
    wcel
    cX
    cS
    wcel
    wa
    cY
    cS
    wcel
    cZ
    cS
    wcel
    wa
    @45
    @35
    wceq
    @42
    ecovdi.8
    ecovdi.9
    ecovdi.6
    syl2an
    eqtrd
    3impdi
    3eqtr4a
    3ecoptocl
end
