include "wcel.mm"
include "cc.mm"
include "cnv.mm"
include "co.mm"
include "cfv.mm"
include "cabs.mm"
include "cmul.mm"
include "wceq.mm"
include "cv.mm"
include "wral.mm"
include "wa.mm"
include "cc0.mm"
include "cn0v.mm"
include "wi.mm"
include "cpv.mm"
include "caddc.mm"
include "cle.mm"
include "wbr.mm"
include "w3a.mm"
include "cop.mm"
include "cvc.mm"
include "cr.mm"
include "wf.mm"
include "eqid.mm"
include "nvi.mm"
include "simp3d.mm"
include "simp2.mm"
include "ralimi.mm"
include "syl.mm"
include "oveq2.mm"
include "fveq2d.mm"
include "fveq2.mm"
include "oveq2d.mm"
include "eqeq12d.mm"
include "oveq1.mm"
include "oveq1d.mm"
include "rspc2v.mm"
include "syl5.mm"
include "3impia.mm"
include "3com13.mm"

theorem nvs
  let cA: class A
  let cB: class B
  let cS: class S
  let cU: class U
  let cN: class N
  let cX: class X
  let vy: setvar y
  let vx: setvar x
  assume nvs.1: |- X = ( BaseSet ` U )
  assume nvs.4: |- S = ( .sOLD ` U )
  assume nvs.6: |- N = ( normCV ` U )


  assert |- ( ( U e. NrmCVec /\ A e. CC /\ B e. X ) -> ( N ` ( A S B ) ) = ( ( abs ` A ) x. ( N ` B ) ) )

  proof
    cB
    cX
    wcel
    #
    cA
    cc
    wcel
    #
    cU
    cnv
    wcel
    #
    cA
    cB
    cS
    co
    #
    cN
    cfv
    #
    cA
    cabs
    cfv
    #
    cB
    cN
    cfv
    #
    cmul
    co
    #
    wceq
    #
    @0
    @1
    @2
    @8
    @2
    vy
    cv
    #
    vx
    cv
    #
    cS
    co
    #
    cN
    cfv
    #
    @9
    cabs
    cfv
    #
    @10
    cN
    cfv
    #
    cmul
    co
    #
    wceq
    #
    vy
    cc
    wral
    #
    vx
    cX
    wral
    #
    @0
    @1
    wa
    @8
    @2
    @14
    cc0
    wceq
    @10
    cU
    cn0v
    cfv
    #
    wceq
    wi
    #
    @17
    @10
    @9
    cU
    cpv
    cfv
    #
    co
    cN
    cfv
    @14
    @9
    cN
    cfv
    caddc
    co
    cle
    wbr
    vy
    cX
    wral
    #
    w3a
    #
    vx
    cX
    wral
    #
    @18
    @2
    @21
    cS
    cop
    cvc
    wcel
    cX
    cr
    cN
    wf
    @24
    vx
    vy
    cS
    cU
    @21
    cN
    cX
    @19
    nvs.1
    @21
    eqid
    nvs.4
    @19
    eqid
    nvs.6
    nvi
    simp3d
    @23
    @17
    vx
    cX
    @20
    @17
    @22
    simp2
    ralimi
    syl
    @16
    @8
    @9
    cB
    cS
    co
    #
    cN
    cfv
    #
    @13
    @6
    cmul
    co
    #
    wceq
    vx
    vy
    cB
    cA
    cX
    cc
    @10
    cB
    wceq
    #
    @12
    @26
    @15
    @27
    @28
    @11
    @25
    cN
    @10
    cB
    @9
    cS
    oveq2
    fveq2d
    @28
    @14
    @6
    @13
    cmul
    @10
    cB
    cN
    fveq2
    oveq2d
    eqeq12d
    @9
    cA
    wceq
    #
    @26
    @4
    @27
    @7
    @29
    @25
    @3
    cN
    @9
    cA
    cB
    cS
    oveq1
    fveq2d
    @29
    @13
    @5
    @6
    cmul
    @9
    cA
    cabs
    fveq2
    oveq1d
    eqeq12d
    rspc2v
    syl5
    3impia
    3com13
end
