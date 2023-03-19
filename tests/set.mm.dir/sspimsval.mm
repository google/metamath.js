include "cnv.mm"
include "wcel.mm"
include "wa.mm"
include "cnsb.mm"
include "cfv.mm"
include "co.mm"
include "cnmcv.mm"
include "wceq.mm"
include "sspnv.mm"
include "eqid.mm"
include "nvmcl.mm"
include "3expb.mm"
include "sylan.mm"
include "sspnval.mm"
include "3expa.mm"
include "syldan.mm"
include "sspmval.mm"
include "fveq2d.mm"
include "eqtrd.mm"
include "imsdval.mm"
include "cba.mm"
include "sspba.mm"
include "sseld.mm"
include "anim12d.mm"
include "imp.mm"
include "adantlr.mm"
include "3eqtr4d.mm"

theorem sspimsval
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cU: class U
  let cH: class H
  let cW: class W
  let cY: class Y
  let vx: setvar x
  let vy: setvar y
  assume sspims.y: |- Y = ( BaseSet ` W )
  assume sspims.d: |- D = ( IndMet ` U )
  assume sspims.c: |- C = ( IndMet ` W )
  assume sspims.h: |- H = ( SubSp ` U )


  assert |- ( ( ( U e. NrmCVec /\ W e. H ) /\ ( A e. Y /\ B e. Y ) ) -> ( A C B ) = ( A D B ) )

  proof
    cU
    cnv
    wcel
    #
    cW
    cH
    wcel
    #
    wa
    #
    cA
    cY
    wcel
    #
    cB
    cY
    wcel
    #
    wa
    #
    wa
    #
    cA
    cB
    cW
    cnsb
    cfv
    #
    co
    #
    cW
    cnmcv
    cfv
    #
    cfv
    #
    cA
    cB
    cU
    cnsb
    cfv
    #
    co
    #
    cU
    cnmcv
    cfv
    #
    cfv
    #
    cA
    cB
    cC
    co
    #
    cA
    cB
    cD
    co
    #
    @6
    @10
    @8
    @13
    cfv
    #
    @14
    @2
    @5
    @8
    cY
    wcel
    #
    @10
    @17
    wceq
    #
    @2
    cW
    cnv
    wcel
    #
    @5
    @18
    cU
    cH
    cW
    sspims.h
    sspnv
    #
    @20
    @3
    @4
    @18
    cA
    cB
    cW
    @7
    cY
    sspims.y
    @7
    eqid
    #
    nvmcl
    3expb
    sylan
    @0
    @1
    @18
    @19
    @8
    cU
    cH
    @9
    @13
    cW
    cY
    sspims.y
    @13
    eqid
    #
    @9
    eqid
    #
    sspims.h
    sspnval
    3expa
    syldan
    @6
    @8
    @12
    @13
    cA
    cB
    cU
    cH
    @7
    @11
    cW
    cY
    sspims.y
    @11
    eqid
    #
    @22
    sspims.h
    sspmval
    fveq2d
    eqtrd
    @2
    @20
    @5
    @15
    @10
    wceq
    #
    @21
    @20
    @3
    @4
    @26
    cA
    cB
    cC
    cW
    @7
    @9
    cY
    sspims.y
    @22
    @24
    sspims.c
    imsdval
    3expb
    sylan
    @2
    @5
    cA
    cU
    cba
    cfv
    #
    wcel
    #
    cB
    @27
    wcel
    #
    wa
    #
    @16
    @14
    wceq
    #
    @2
    @5
    @30
    @2
    @3
    @28
    @4
    @29
    @2
    cY
    @27
    cA
    cU
    cH
    cW
    @27
    cY
    @27
    eqid
    #
    sspims.y
    sspims.h
    sspba
    #
    sseld
    @2
    cY
    @27
    cB
    @33
    sseld
    anim12d
    imp
    @0
    @30
    @31
    @1
    @0
    @28
    @29
    @31
    cA
    cB
    cD
    cU
    @11
    @13
    @27
    @32
    @25
    @23
    sspims.d
    imsdval
    3expb
    adantlr
    syldan
    3eqtr4d
end
