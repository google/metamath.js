include "cc.mm"
include "wcel.mm"
include "w3a.mm"
include "cvc.mm"
include "cmul.mm"
include "co.mm"
include "wceq.mm"
include "wi.mm"
include "cv.mm"
include "wral.mm"
include "cablo.mm"
include "cxp.mm"
include "wf.mm"
include "c1.mm"
include "caddc.mm"
include "wa.mm"
include "vciOLD.mm"
include "simpr.mm"
include "ralimi.mm"
include "adantl.mm"
include "3ad2ant3.mm"
include "syl.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "eqeq12d.mm"
include "oveq1.mm"
include "oveq1d.mm"
include "rspc3v.mm"
include "syl5.mm"
include "3coml.mm"
include "impcom.mm"

theorem vcass
  let cA: class A
  let cB: class B
  let cC: class C
  let cS: class S
  let cG: class G
  let cW: class W
  let cX: class X
  let vg: setvar g
  let vs: setvar s
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume vciOLD.1: |- G = ( 1st ` W )
  assume vciOLD.2: |- S = ( 2nd ` W )
  assume vciOLD.3: |- X = ran G


  assert |- ( ( W e. CVecOLD /\ ( A e. CC /\ B e. CC /\ C e. X ) ) -> ( ( A x. B ) S C ) = ( A S ( B S C ) ) )

  proof
    cA
    cc
    wcel
    #
    cB
    cc
    wcel
    #
    cC
    cX
    wcel
    #
    w3a
    cW
    cvc
    wcel
    #
    cA
    cB
    cmul
    co
    #
    cC
    cS
    co
    #
    cA
    cB
    cC
    cS
    co
    #
    cS
    co
    #
    wceq
    #
    @2
    @0
    @1
    @3
    @8
    wi
    @3
    vy
    cv
    #
    vz
    cv
    #
    cmul
    co
    #
    vx
    cv
    #
    cS
    co
    #
    @9
    @10
    @12
    cS
    co
    #
    cS
    co
    #
    wceq
    #
    vz
    cc
    wral
    #
    vy
    cc
    wral
    #
    vx
    cX
    wral
    #
    @2
    @0
    @1
    w3a
    @8
    @3
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
    c1
    @12
    cS
    co
    @12
    wceq
    #
    @9
    @12
    @10
    cG
    co
    cS
    co
    @9
    @12
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
    #
    @9
    @10
    caddc
    co
    @12
    cS
    co
    @23
    @14
    cG
    co
    wceq
    #
    @16
    wa
    #
    vz
    cc
    wral
    #
    wa
    #
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
    @19
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
    @31
    @20
    @19
    @21
    @30
    @18
    vx
    cX
    @29
    @18
    @22
    @28
    @17
    vy
    cc
    @27
    @17
    @24
    @26
    @16
    vz
    cc
    @25
    @16
    simpr
    ralimi
    adantl
    ralimi
    adantl
    ralimi
    3ad2ant3
    syl
    @16
    @8
    @11
    cC
    cS
    co
    #
    @9
    @10
    cC
    cS
    co
    #
    cS
    co
    #
    wceq
    cA
    @10
    cmul
    co
    #
    cC
    cS
    co
    #
    cA
    @33
    cS
    co
    #
    wceq
    vx
    vy
    vz
    cC
    cA
    cB
    cX
    cc
    cc
    @12
    cC
    wceq
    #
    @13
    @32
    @15
    @34
    @12
    cC
    @11
    cS
    oveq2
    @38
    @14
    @33
    @9
    cS
    @12
    cC
    @10
    cS
    oveq2
    oveq2d
    eqeq12d
    @9
    cA
    wceq
    #
    @32
    @36
    @34
    @37
    @39
    @11
    @35
    cC
    cS
    @9
    cA
    @10
    cmul
    oveq1
    oveq1d
    @9
    cA
    @33
    cS
    oveq1
    eqeq12d
    @10
    cB
    wceq
    #
    @36
    @5
    @37
    @7
    @40
    @35
    @4
    cC
    cS
    @10
    cB
    cA
    cmul
    oveq2
    oveq1d
    @40
    @33
    @6
    cA
    cS
    @10
    cB
    cC
    cS
    oveq1
    oveq2d
    eqeq12d
    rspc3v
    syl5
    3coml
    impcom
end
