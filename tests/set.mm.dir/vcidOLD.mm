include "cvc.mm"
include "wcel.mm"
include "c1.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "cablo.mm"
include "cc.mm"
include "cxp.mm"
include "wf.mm"
include "caddc.mm"
include "cmul.mm"
include "wa.mm"
include "w3a.mm"
include "vciOLD.mm"
include "simpl.mm"
include "ralimi.mm"
include "3ad2ant3.mm"
include "syl.mm"
include "oveq2.mm"
include "id.mm"
include "eqeq12d.mm"
include "rspccva.mm"
include "sylan.mm"

theorem vcidOLD
  let cA: class A
  let cS: class S
  let cG: class G
  let cW: class W
  let cX: class X
  let vg: setvar g
  let vs: setvar s
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let cC: class C
  assume vciOLD.1: |- G = ( 1st ` W )
  assume vciOLD.2: |- S = ( 2nd ` W )
  assume vciOLD.3: |- X = ran G


  assert |- ( ( W e. CVecOLD /\ A e. X ) -> ( 1 S A ) = A )

  proof
    cW
    cvc
    wcel
    #
    c1
    vx
    cv
    #
    cS
    co
    #
    @1
    wceq
    #
    vx
    cX
    wral
    #
    cA
    cX
    wcel
    c1
    cA
    cS
    co
    #
    cA
    wceq
    #
    @0
    cG
    cablo
    wcel
    #
    cc
    cX
    cxp
    cX
    cS
    wf
    #
    @3
    vy
    cv
    #
    @1
    vz
    cv
    #
    cG
    co
    cS
    co
    @9
    @1
    cS
    co
    #
    @9
    @10
    cS
    co
    cG
    co
    wceq
    vz
    cX
    wral
    @9
    @10
    caddc
    co
    @1
    cS
    co
    @11
    @10
    @1
    cS
    co
    #
    cG
    co
    wceq
    @9
    @10
    cmul
    co
    @1
    cS
    co
    @9
    @12
    cS
    co
    wceq
    wa
    vz
    cc
    wral
    wa
    vy
    cc
    wral
    #
    wa
    #
    vx
    cX
    wral
    #
    w3a
    @4
    vx
    vy
    vz
    cS
    cG
    cW
    cX
    vciOLD.1
    vciOLD.2
    vciOLD.3
    vciOLD
    @15
    @7
    @4
    @8
    @14
    @3
    vx
    cX
    @3
    @13
    simpl
    ralimi
    3ad2ant3
    syl
    @3
    @6
    vx
    cA
    cX
    @1
    cA
    wceq
    #
    @2
    @5
    @1
    cA
    @1
    cA
    c1
    cS
    oveq2
    @16
    id
    eqeq12d
    rspccva
    sylan
end
