include "cgr.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "cv.mm"
include "crab.mm"
include "crio.mm"
include "grpoinvval.mm"
include "wreu.mm"
include "grpoinveu.mm"
include "riotacl2.mm"
include "syl.mm"
include "eqeltrd.mm"
include "wi.mm"
include "wral.mm"
include "wrex.mm"
include "w3a.mm"
include "wb.mm"
include "simpl.mm"
include "rgenw.mm"
include "a1i.mm"
include "grpoidinv2.mm"
include "simprd.mm"
include "3jca.mm"
include "reupick2.mm"
include "sylan.mm"
include "rabbidva.mm"
include "eleqtrd.mm"
include "oveq1.mm"
include "eqeq1d.mm"
include "oveq2.mm"
include "anbi12d.mm"
include "elrab.mm"
include "sylib.mm"

theorem grpoinv
  let cA: class A
  let cU: class U
  let cG: class G
  let cN: class N
  let cX: class X
  let vy: setvar y
  assume grpinv.1: |- X = ran G
  assume grpinv.2: |- U = ( GId ` G )
  assume grpinv.3: |- N = ( inv ` G )


  assert |- ( ( G e. GrpOp /\ A e. X ) -> ( ( ( N ` A ) G A ) = U /\ ( A G ( N ` A ) ) = U ) )

  proof
    cG
    cgr
    wcel
    cA
    cX
    wcel
    wa
    #
    cA
    cN
    cfv
    #
    cX
    wcel
    #
    @1
    cA
    cG
    co
    #
    cU
    wceq
    #
    cA
    @1
    cG
    co
    #
    cU
    wceq
    #
    wa
    #
    @0
    @1
    vy
    cv
    #
    cA
    cG
    co
    #
    cU
    wceq
    #
    cA
    @8
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
    crab
    #
    wcel
    @2
    @7
    wa
    @0
    @1
    @10
    vy
    cX
    crab
    #
    @14
    @0
    @1
    @10
    vy
    cX
    crio
    #
    @15
    vy
    cA
    cU
    cG
    cN
    cX
    grpinv.1
    grpinv.2
    grpinv.3
    grpoinvval
    @0
    @10
    vy
    cX
    wreu
    #
    @16
    @15
    wcel
    vy
    cA
    cU
    cG
    cX
    grpinv.1
    grpinv.2
    grpoinveu
    #
    @10
    vy
    cX
    riotacl2
    syl
    eqeltrd
    @0
    @10
    @13
    vy
    cX
    @0
    @13
    @10
    wi
    #
    vy
    cX
    wral
    #
    @13
    vy
    cX
    wrex
    #
    @17
    w3a
    @8
    cX
    wcel
    @10
    @13
    wb
    @0
    @20
    @21
    @17
    @20
    @0
    @19
    vy
    cX
    @10
    @12
    simpl
    rgenw
    a1i
    @0
    cU
    cA
    cG
    co
    cA
    wceq
    cA
    cU
    cG
    co
    cA
    wceq
    wa
    @21
    vy
    cA
    cU
    cG
    cX
    grpinv.1
    grpinv.2
    grpoidinv2
    simprd
    @18
    3jca
    @10
    @13
    vy
    cX
    reupick2
    sylan
    rabbidva
    eleqtrd
    @13
    @7
    vy
    @1
    cX
    @8
    @1
    wceq
    #
    @10
    @4
    @12
    @6
    @22
    @9
    @3
    cU
    @8
    @1
    cA
    cG
    oveq1
    eqeq1d
    @22
    @11
    @5
    cU
    @8
    @1
    cA
    cG
    oveq2
    eqeq1d
    anbi12d
    elrab
    sylib
    simprd
end
