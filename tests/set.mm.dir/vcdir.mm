include "cc.mm"
include "wcel.mm"
include "w3a.mm"
include "cvc.mm"
include "caddc.mm"
include "co.mm"
include "wceq.mm"
include "wi.mm"
include "cv.mm"
include "wral.mm"
include "cablo.mm"
include "cxp.mm"
include "wf.mm"
include "c1.mm"
include "cmul.mm"
include "wa.mm"
include "vciOLD.mm"
include "simpl.mm"
include "ralimi.mm"
include "adantl.mm"
include "3ad2ant3.mm"
include "syl.mm"
include "oveq2.mm"
include "oveq12d.mm"
include "eqeq12d.mm"
include "oveq1.mm"
include "oveq1d.mm"
include "oveq2d.mm"
include "rspc3v.mm"
include "syl5.mm"
include "3coml.mm"
include "impcom.mm"

theorem vcdir
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


  assert |- ( ( W e. CVecOLD /\ ( A e. CC /\ B e. CC /\ C e. X ) ) -> ( ( A + B ) S C ) = ( ( A S C ) G ( B S C ) ) )

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
    caddc
    co
    #
    cC
    cS
    co
    #
    cA
    cC
    cS
    co
    #
    cB
    cC
    cS
    co
    #
    cG
    co
    #
    wceq
    #
    @2
    @0
    @1
    @3
    @9
    wi
    @3
    vy
    cv
    #
    vz
    cv
    #
    caddc
    co
    #
    vx
    cv
    #
    cS
    co
    #
    @10
    @13
    cS
    co
    #
    @11
    @13
    cS
    co
    #
    cG
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
    @13
    cS
    co
    @13
    wceq
    #
    @10
    @13
    @11
    cG
    co
    cS
    co
    @15
    @10
    @11
    cS
    co
    cG
    co
    wceq
    vz
    cX
    wral
    #
    @18
    @10
    @11
    cmul
    co
    @13
    cS
    co
    @10
    @16
    cS
    co
    wceq
    #
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
    @32
    @22
    @21
    @23
    @31
    @20
    vx
    cX
    @30
    @20
    @24
    @29
    @19
    vy
    cc
    @28
    @19
    @25
    @27
    @18
    vz
    cc
    @18
    @26
    simpl
    ralimi
    adantl
    ralimi
    adantl
    ralimi
    3ad2ant3
    syl
    @18
    @9
    @12
    cC
    cS
    co
    #
    @10
    cC
    cS
    co
    #
    @11
    cC
    cS
    co
    #
    cG
    co
    #
    wceq
    cA
    @11
    caddc
    co
    #
    cC
    cS
    co
    #
    @6
    @35
    cG
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
    @13
    cC
    wceq
    #
    @14
    @33
    @17
    @36
    @13
    cC
    @12
    cS
    oveq2
    @40
    @15
    @34
    @16
    @35
    cG
    @13
    cC
    @10
    cS
    oveq2
    @13
    cC
    @11
    cS
    oveq2
    oveq12d
    eqeq12d
    @10
    cA
    wceq
    #
    @33
    @38
    @36
    @39
    @41
    @12
    @37
    cC
    cS
    @10
    cA
    @11
    caddc
    oveq1
    oveq1d
    @41
    @34
    @6
    @35
    cG
    @10
    cA
    cC
    cS
    oveq1
    oveq1d
    eqeq12d
    @11
    cB
    wceq
    #
    @38
    @5
    @39
    @8
    @42
    @37
    @4
    cC
    cS
    @11
    cB
    cA
    caddc
    oveq2
    oveq1d
    @42
    @35
    @7
    @6
    cG
    @11
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
