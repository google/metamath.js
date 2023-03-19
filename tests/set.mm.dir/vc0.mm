include "cvc.mm"
include "wcel.mm"
include "wa.mm"
include "cc0.mm"
include "co.mm"
include "wceq.mm"
include "c1.mm"
include "vc0rid.mm"
include "caddc.mm"
include "1p0e1.mm"
include "oveq1i.mm"
include "cc.mm"
include "0cn.mm"
include "ax-1cn.mm"
include "vcdir.mm"
include "mp3anr1.mm"
include "mpanr1.mm"
include "vcidOLD.mm"
include "3eqtr3a.mm"
include "oveq1d.mm"
include "3eqtr2rd.mm"
include "w3a.mm"
include "wb.mm"
include "vccl.mm"
include "mp3an2.mm"
include "vczcl.mm"
include "adantr.mm"
include "simpr.mm"
include "3jca.mm"
include "vclcan.mm"
include "syldan.mm"
include "mpbid.mm"

theorem vc0
  let cA: class A
  let cS: class S
  let cG: class G
  let cW: class W
  let cX: class X
  let cZ: class Z
  assume vc0.1: |- G = ( 1st ` W )
  assume vc0.2: |- S = ( 2nd ` W )
  assume vc0.3: |- X = ran G
  assume vc0.4: |- Z = ( GId ` G )


  assert |- ( ( W e. CVecOLD /\ A e. X ) -> ( 0 S A ) = Z )

  proof
    cW
    cvc
    wcel
    #
    cA
    cX
    wcel
    #
    wa
    #
    cA
    cc0
    cA
    cS
    co
    #
    cG
    co
    #
    cA
    cZ
    cG
    co
    #
    wceq
    #
    @3
    cZ
    wceq
    #
    @2
    @5
    cA
    c1
    cA
    cS
    co
    #
    @3
    cG
    co
    #
    @4
    cA
    cG
    cW
    cX
    cZ
    vc0.1
    vc0.3
    vc0.4
    vc0rid
    @2
    c1
    cc0
    caddc
    co
    #
    cA
    cS
    co
    #
    @8
    @9
    cA
    @10
    c1
    cA
    cS
    1p0e1
    oveq1i
    @0
    cc0
    cc
    wcel
    #
    @1
    @11
    @9
    wceq
    #
    0cn
    @0
    c1
    cc
    wcel
    @12
    @1
    @13
    ax-1cn
    c1
    cc0
    cA
    cS
    cG
    cW
    cX
    vc0.1
    vc0.2
    vc0.3
    vcdir
    mp3anr1
    mpanr1
    cA
    cS
    cG
    cW
    cX
    vc0.1
    vc0.2
    vc0.3
    vcidOLD
    #
    3eqtr3a
    @2
    @8
    cA
    @3
    cG
    @14
    oveq1d
    3eqtr2rd
    @0
    @1
    @3
    cX
    wcel
    #
    cZ
    cX
    wcel
    #
    @1
    w3a
    @6
    @7
    wb
    @2
    @15
    @16
    @1
    @0
    @12
    @1
    @15
    0cn
    cc0
    cA
    cS
    cG
    cW
    cX
    vc0.1
    vc0.2
    vc0.3
    vccl
    mp3an2
    @0
    @16
    @1
    cG
    cW
    cX
    cZ
    vc0.1
    vc0.3
    vc0.4
    vczcl
    adantr
    @0
    @1
    simpr
    3jca
    @3
    cZ
    cA
    cG
    cW
    cX
    vc0.1
    vc0.3
    vclcan
    syldan
    mpbid
end
