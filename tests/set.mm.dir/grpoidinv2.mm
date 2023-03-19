include "cgr.mm"
include "wcel.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "wrex.mm"
include "wral.mm"
include "crab.mm"
include "crio.mm"
include "grpoidval.mm"
include "wreu.mm"
include "grpoideu.mm"
include "riotacl2.mm"
include "syl.mm"
include "eqeltrd.mm"
include "wi.mm"
include "w3a.mm"
include "wb.mm"
include "simpll.mm"
include "ralimi.mm"
include "rgenw.mm"
include "a1i.mm"
include "grpoidinv.mm"
include "3jca.mm"
include "reupick2.mm"
include "sylan.mm"
include "rabbidva.mm"
include "eleqtrd.mm"
include "oveq1.mm"
include "eqeq1d.mm"
include "oveq2.mm"
include "anbi12d.mm"
include "eqeq2.mm"
include "rexbidv.mm"
include "ralbidv.mm"
include "elrab.mm"
include "sylib.mm"
include "simprd.mm"
include "id.mm"
include "eqeq12d.mm"
include "rspccva.mm"

theorem grpoidinv2
  let vy: setvar y
  let cA: class A
  let cU: class U
  let cG: class G
  let cX: class X
  let vx: setvar x
  let vu: setvar u
  assume grpoidval.1: |- X = ran G
  assume grpoidval.2: |- U = ( GId ` G )

  disjoint A y
  disjoint G y
  disjoint U y
  disjoint X y
  disjoint x y
  disjoint A x
  disjoint u x
  disjoint u y
  disjoint G u
  disjoint G x
  disjoint U u
  disjoint U x
  disjoint X u
  disjoint X x
  assert |- ( ( G e. GrpOp /\ A e. X ) -> ( ( ( U G A ) = A /\ ( A G U ) = A ) /\ E. y e. X ( ( y G A ) = U /\ ( A G y ) = U ) ) )

  proof
    cG
    cgr
    wcel
    #
    cU
    vx
    cv
    #
    cG
    co
    #
    @1
    wceq
    #
    @1
    cU
    cG
    co
    #
    @1
    wceq
    #
    wa
    #
    vy
    cv
    #
    @1
    cG
    co
    #
    cU
    wceq
    #
    @1
    @7
    cG
    co
    #
    cU
    wceq
    #
    wa
    #
    vy
    cX
    wrex
    #
    wa
    #
    vx
    cX
    wral
    #
    cA
    cX
    wcel
    cU
    cA
    cG
    co
    #
    cA
    wceq
    #
    cA
    cU
    cG
    co
    #
    cA
    wceq
    #
    wa
    #
    @7
    cA
    cG
    co
    #
    cU
    wceq
    #
    cA
    @7
    cG
    co
    #
    cU
    wceq
    #
    wa
    #
    vy
    cX
    wrex
    #
    wa
    #
    @0
    cU
    cX
    wcel
    #
    @15
    @0
    cU
    vu
    cv
    #
    @1
    cG
    co
    #
    @1
    wceq
    #
    @1
    @29
    cG
    co
    #
    @1
    wceq
    #
    wa
    #
    @8
    @29
    wceq
    #
    @10
    @29
    wceq
    #
    wa
    #
    vy
    cX
    wrex
    #
    wa
    #
    vx
    cX
    wral
    #
    vu
    cX
    crab
    #
    wcel
    @28
    @15
    wa
    @0
    cU
    @31
    vx
    cX
    wral
    #
    vu
    cX
    crab
    #
    @41
    @0
    cU
    @42
    vu
    cX
    crio
    #
    @43
    vx
    vu
    cU
    cG
    cX
    grpoidval.1
    grpoidval.2
    grpoidval
    @0
    @42
    vu
    cX
    wreu
    #
    @44
    @43
    wcel
    vx
    vu
    cG
    cX
    grpoidval.1
    grpoideu
    #
    @42
    vu
    cX
    riotacl2
    syl
    eqeltrd
    @0
    @42
    @40
    vu
    cX
    @0
    @40
    @42
    wi
    #
    vu
    cX
    wral
    #
    @40
    vu
    cX
    wrex
    #
    @45
    w3a
    @29
    cX
    wcel
    @42
    @40
    wb
    @0
    @48
    @49
    @45
    @48
    @0
    @47
    vu
    cX
    @39
    @31
    vx
    cX
    @31
    @33
    @38
    simpll
    ralimi
    rgenw
    a1i
    vx
    vy
    vu
    cG
    cX
    grpoidval.1
    grpoidinv
    @46
    3jca
    @42
    @40
    vu
    cX
    reupick2
    sylan
    rabbidva
    eleqtrd
    @40
    @15
    vu
    cU
    cX
    @29
    cU
    wceq
    #
    @39
    @14
    vx
    cX
    @50
    @34
    @6
    @38
    @13
    @50
    @31
    @3
    @33
    @5
    @50
    @30
    @2
    @1
    @29
    cU
    @1
    cG
    oveq1
    eqeq1d
    @50
    @32
    @4
    @1
    @29
    cU
    @1
    cG
    oveq2
    eqeq1d
    anbi12d
    @50
    @37
    @12
    vy
    cX
    @50
    @35
    @9
    @36
    @11
    @29
    cU
    @8
    eqeq2
    @29
    cU
    @10
    eqeq2
    anbi12d
    rexbidv
    anbi12d
    ralbidv
    elrab
    sylib
    simprd
    @14
    @27
    vx
    cA
    cX
    @1
    cA
    wceq
    #
    @6
    @20
    @13
    @26
    @51
    @3
    @17
    @5
    @19
    @51
    @2
    @16
    @1
    cA
    @1
    cA
    cU
    cG
    oveq2
    @51
    id
    #
    eqeq12d
    @51
    @4
    @18
    @1
    cA
    @1
    cA
    cU
    cG
    oveq1
    @52
    eqeq12d
    anbi12d
    @51
    @12
    @25
    vy
    cX
    @51
    @9
    @22
    @11
    @24
    @51
    @8
    @21
    cU
    @1
    cA
    @7
    cG
    oveq2
    eqeq1d
    @51
    @10
    @23
    cU
    @1
    cA
    @7
    cG
    oveq1
    eqeq1d
    anbi12d
    rexbidv
    anbi12d
    rspccva
    sylan
end
