include "cnv.mm"
include "wcel.mm"
include "w3a.mm"
include "cv.mm"
include "co.mm"
include "cfv.mm"
include "wceq.mm"
include "wral.mm"
include "cc.mm"
include "wf.mm"
include "wa.mm"
include "islno.mm"
include "biimp3a.mm"
include "simprd.mm"
include "oveq1.mm"
include "oveq1d.mm"
include "fveq2d.mm"
include "eqeq12d.mm"
include "oveq2.mm"
include "fveq2.mm"
include "oveq2d.mm"
include "rspc3v.mm"
include "mpan9.mm"

theorem lnolin
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let cS: class S
  let cT: class T
  let cU: class U
  let cG: class G
  let cH: class H
  let cL: class L
  let cW: class W
  let cX: class X
  let cY: class Y
  let vt: setvar t
  let vu: setvar u
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume lnoval.1: |- X = ( BaseSet ` U )
  assume lnoval.2: |- Y = ( BaseSet ` W )
  assume lnoval.3: |- G = ( +v ` U )
  assume lnoval.4: |- H = ( +v ` W )
  assume lnoval.5: |- R = ( .sOLD ` U )
  assume lnoval.6: |- S = ( .sOLD ` W )
  assume lnoval.7: |- L = ( U LnOp W )


  assert |- ( ( ( U e. NrmCVec /\ W e. NrmCVec /\ T e. L ) /\ ( A e. CC /\ B e. X /\ C e. X ) ) -> ( T ` ( ( A R B ) G C ) ) = ( ( A S ( T ` B ) ) H ( T ` C ) ) )

  proof
    cU
    cnv
    wcel
    #
    cW
    cnv
    wcel
    #
    cT
    cL
    wcel
    #
    w3a
    #
    vu
    cv
    #
    vw
    cv
    #
    cR
    co
    #
    vt
    cv
    #
    cG
    co
    #
    cT
    cfv
    #
    @4
    @5
    cT
    cfv
    #
    cS
    co
    #
    @7
    cT
    cfv
    #
    cH
    co
    #
    wceq
    #
    vt
    cX
    wral
    vw
    cX
    wral
    vu
    cc
    wral
    #
    cA
    cc
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
    cR
    co
    #
    cC
    cG
    co
    #
    cT
    cfv
    #
    cA
    cB
    cT
    cfv
    #
    cS
    co
    #
    cC
    cT
    cfv
    #
    cH
    co
    #
    wceq
    #
    @3
    cX
    cY
    cT
    wf
    #
    @15
    @0
    @1
    @2
    @24
    @15
    wa
    vu
    vw
    vt
    cR
    cS
    cT
    cU
    cG
    cH
    cL
    cW
    cX
    cY
    lnoval.1
    lnoval.2
    lnoval.3
    lnoval.4
    lnoval.5
    lnoval.6
    lnoval.7
    islno
    biimp3a
    simprd
    @14
    @23
    cA
    @5
    cR
    co
    #
    @7
    cG
    co
    #
    cT
    cfv
    #
    cA
    @10
    cS
    co
    #
    @12
    cH
    co
    #
    wceq
    @16
    @7
    cG
    co
    #
    cT
    cfv
    #
    @20
    @12
    cH
    co
    #
    wceq
    vu
    vw
    vt
    cA
    cB
    cC
    cc
    cX
    cX
    @4
    cA
    wceq
    #
    @9
    @27
    @13
    @29
    @33
    @8
    @26
    cT
    @33
    @6
    @25
    @7
    cG
    @4
    cA
    @5
    cR
    oveq1
    oveq1d
    fveq2d
    @33
    @11
    @28
    @12
    cH
    @4
    cA
    @10
    cS
    oveq1
    oveq1d
    eqeq12d
    @5
    cB
    wceq
    #
    @27
    @31
    @29
    @32
    @34
    @26
    @30
    cT
    @34
    @25
    @16
    @7
    cG
    @5
    cB
    cA
    cR
    oveq2
    oveq1d
    fveq2d
    @34
    @28
    @20
    @12
    cH
    @34
    @10
    @19
    cA
    cS
    @5
    cB
    cT
    fveq2
    oveq2d
    oveq1d
    eqeq12d
    @7
    cC
    wceq
    #
    @31
    @18
    @32
    @22
    @35
    @30
    @17
    cT
    @7
    cC
    @16
    cG
    oveq2
    fveq2d
    @35
    @12
    @21
    @20
    cH
    @7
    cC
    cT
    fveq2
    oveq2d
    eqeq12d
    rspc3v
    mpan9
end
