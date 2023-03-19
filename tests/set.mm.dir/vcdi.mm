include "cc.mm"
include "wcel.mm"
include "w3a.mm"
include "cvc.mm"
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
include "cmul.mm"
include "wa.mm"
include "vciOLD.mm"
include "simpl.mm"
include "ralimi.mm"
include "adantl.mm"
include "3ad2ant3.mm"
include "syl.mm"
include "oveq1.mm"
include "oveq2d.mm"
include "oveq2.mm"
include "oveq1d.mm"
include "eqeq12d.mm"
include "oveq12d.mm"
include "rspc3v.mm"
include "syl5.mm"
include "3com12.mm"
include "impcom.mm"

theorem vcdi
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


  assert |- ( ( W e. CVecOLD /\ ( A e. CC /\ B e. X /\ C e. X ) ) -> ( A S ( B G C ) ) = ( ( A S B ) G ( A S C ) ) )

  proof
    cA
    cc
    wcel
    #
    cB
    cX
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
    cC
    cG
    co
    #
    cS
    co
    #
    cA
    cB
    cS
    co
    #
    cA
    cC
    cS
    co
    #
    cG
    co
    #
    wceq
    #
    @1
    @0
    @2
    @3
    @9
    wi
    @3
    vy
    cv
    #
    vx
    cv
    #
    vz
    cv
    #
    cG
    co
    #
    cS
    co
    #
    @10
    @11
    cS
    co
    #
    @10
    @12
    cS
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
    #
    vy
    cc
    wral
    #
    vx
    cX
    wral
    #
    @1
    @0
    @2
    w3a
    @9
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
    @11
    cS
    co
    @11
    wceq
    #
    @19
    @10
    @12
    caddc
    co
    @11
    cS
    co
    @15
    @12
    @11
    cS
    co
    #
    cG
    co
    wceq
    @10
    @12
    cmul
    co
    @11
    cS
    co
    @10
    @25
    cS
    co
    wceq
    wa
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
    @21
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
    @30
    @22
    @21
    @23
    @29
    @20
    vx
    cX
    @28
    @20
    @24
    @27
    @19
    vy
    cc
    @19
    @26
    simpl
    ralimi
    adantl
    ralimi
    3ad2ant3
    syl
    @18
    @9
    @10
    cB
    @12
    cG
    co
    #
    cS
    co
    #
    @10
    cB
    cS
    co
    #
    @16
    cG
    co
    #
    wceq
    cA
    @31
    cS
    co
    #
    @6
    cA
    @12
    cS
    co
    #
    cG
    co
    #
    wceq
    vx
    vy
    vz
    cB
    cA
    cC
    cX
    cc
    cX
    @11
    cB
    wceq
    #
    @14
    @32
    @17
    @34
    @38
    @13
    @31
    @10
    cS
    @11
    cB
    @12
    cG
    oveq1
    oveq2d
    @38
    @15
    @33
    @16
    cG
    @11
    cB
    @10
    cS
    oveq2
    oveq1d
    eqeq12d
    @10
    cA
    wceq
    #
    @32
    @35
    @34
    @37
    @10
    cA
    @31
    cS
    oveq1
    @39
    @33
    @6
    @16
    @36
    cG
    @10
    cA
    cB
    cS
    oveq1
    @10
    cA
    @12
    cS
    oveq1
    oveq12d
    eqeq12d
    @12
    cC
    wceq
    #
    @35
    @5
    @37
    @8
    @40
    @31
    @4
    cA
    cS
    @12
    cC
    cB
    cG
    oveq2
    oveq2d
    @40
    @36
    @7
    @6
    cG
    @12
    cC
    cA
    cS
    oveq2
    oveq2d
    eqeq12d
    rspc3v
    syl5
    3com12
    impcom
end
