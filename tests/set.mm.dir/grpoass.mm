include "cgr.mm"
include "wcel.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "w3a.mm"
include "cxp.mm"
include "wf.mm"
include "wrex.mm"
include "wa.mm"
include "isgrpo.mm"
include "ibi.mm"
include "simp2d.mm"
include "oveq1.mm"
include "oveq1d.mm"
include "eqeq12d.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "rspc3v.mm"
include "mpan9.mm"

theorem grpoass
  let cA: class A
  let cB: class B
  let cC: class C
  let cG: class G
  let cX: class X
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vu: setvar u
  let cU: class U
  assume grpfo.1: |- X = ran G


  assert |- ( ( G e. GrpOp /\ ( A e. X /\ B e. X /\ C e. X ) ) -> ( ( A G B ) G C ) = ( A G ( B G C ) ) )

  proof
    cG
    cgr
    wcel
    #
    vx
    cv
    #
    vy
    cv
    #
    cG
    co
    #
    vz
    cv
    #
    cG
    co
    #
    @1
    @2
    @4
    cG
    co
    #
    cG
    co
    #
    wceq
    #
    vz
    cX
    wral
    vy
    cX
    wral
    vx
    cX
    wral
    #
    cA
    cX
    wcel
    cB
    cX
    wcel
    cC
    cX
    wcel
    w3a
    cA
    cB
    cG
    co
    #
    cC
    cG
    co
    #
    cA
    cB
    cC
    cG
    co
    #
    cG
    co
    #
    wceq
    #
    @0
    cX
    cX
    cxp
    cX
    cG
    wf
    #
    @9
    vu
    cv
    #
    @1
    cG
    co
    @1
    wceq
    @2
    @1
    cG
    co
    @16
    wceq
    vy
    cX
    wrex
    wa
    vx
    cX
    wral
    vu
    cX
    wrex
    #
    @0
    @15
    @9
    @17
    w3a
    vx
    vy
    vz
    vu
    cgr
    cG
    cX
    grpfo.1
    isgrpo
    ibi
    simp2d
    @8
    @14
    cA
    @2
    cG
    co
    #
    @4
    cG
    co
    #
    cA
    @6
    cG
    co
    #
    wceq
    @10
    @4
    cG
    co
    #
    cA
    cB
    @4
    cG
    co
    #
    cG
    co
    #
    wceq
    vx
    vy
    vz
    cA
    cB
    cC
    cX
    cX
    cX
    @1
    cA
    wceq
    #
    @5
    @19
    @7
    @20
    @24
    @3
    @18
    @4
    cG
    @1
    cA
    @2
    cG
    oveq1
    oveq1d
    @1
    cA
    @6
    cG
    oveq1
    eqeq12d
    @2
    cB
    wceq
    #
    @19
    @21
    @20
    @23
    @25
    @18
    @10
    @4
    cG
    @2
    cB
    cA
    cG
    oveq2
    oveq1d
    @25
    @6
    @22
    cA
    cG
    @2
    cB
    @4
    cG
    oveq1
    oveq2d
    eqeq12d
    @4
    cC
    wceq
    #
    @21
    @11
    @23
    @13
    @4
    cC
    @10
    cG
    oveq2
    @26
    @22
    @12
    cA
    cG
    @4
    cC
    cB
    cG
    oveq2
    oveq2d
    eqeq12d
    rspc3v
    mpan9
end
