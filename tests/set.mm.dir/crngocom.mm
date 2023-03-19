include "ccring.mm"
include "wcel.mm"
include "co.mm"
include "wceq.mm"
include "cv.mm"
include "wral.mm"
include "wa.mm"
include "crngo.mm"
include "iscrngo2.mm"
include "simprbi.mm"
include "oveq1.mm"
include "oveq2.mm"
include "eqeq12d.mm"
include "rspc2v.mm"
include "mpan9.mm"
include "3impb.mm"

theorem crngocom
  let cA: class A
  let cB: class B
  let cR: class R
  let cG: class G
  let cH: class H
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  assume crngocom.1: |- G = ( 1st ` R )
  assume crngocom.2: |- H = ( 2nd ` R )
  assume crngocom.3: |- X = ran G


  assert |- ( ( R e. CRingOps /\ A e. X /\ B e. X ) -> ( A H B ) = ( B H A ) )

  proof
    cR
    ccring
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
    cA
    cB
    cH
    co
    #
    cB
    cA
    cH
    co
    #
    wceq
    #
    @0
    vx
    cv
    #
    vy
    cv
    #
    cH
    co
    #
    @7
    @6
    cH
    co
    #
    wceq
    #
    vy
    cX
    wral
    vx
    cX
    wral
    #
    @1
    @2
    wa
    @5
    @0
    cR
    crngo
    wcel
    @11
    vx
    vy
    cR
    cG
    cH
    cX
    crngocom.1
    crngocom.2
    crngocom.3
    iscrngo2
    simprbi
    @10
    @5
    cA
    @7
    cH
    co
    #
    @7
    cA
    cH
    co
    #
    wceq
    vx
    vy
    cA
    cB
    cX
    cX
    @6
    cA
    wceq
    @8
    @12
    @9
    @13
    @6
    cA
    @7
    cH
    oveq1
    @6
    cA
    @7
    cH
    oveq2
    eqeq12d
    @7
    cB
    wceq
    @12
    @3
    @13
    @4
    @7
    cB
    cA
    cH
    oveq2
    @7
    cB
    cA
    cH
    oveq1
    eqeq12d
    rspc2v
    mpan9
    3impb
end
