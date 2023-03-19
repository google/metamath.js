include "cnv.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "wi.mm"
include "cv.mm"
include "cns.mm"
include "co.mm"
include "cabs.mm"
include "cmul.mm"
include "cc.mm"
include "wral.mm"
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
include "simp1.mm"
include "ralimi.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "eqeq1.mm"
include "imbi12d.mm"
include "rspccv.mm"
include "3syl.mm"
include "imp.mm"
include "nvz0.mm"
include "sylan9eqr.mm"
include "ex.mm"
include "adantr.mm"
include "impbid.mm"

theorem nvz
  let cA: class A
  let cU: class U
  let cN: class N
  let cX: class X
  let cZ: class Z
  let vx: setvar x
  let vy: setvar y
  assume nvz.1: |- X = ( BaseSet ` U )
  assume nvz.5: |- Z = ( 0vec ` U )
  assume nvz.6: |- N = ( normCV ` U )


  assert |- ( ( U e. NrmCVec /\ A e. X ) -> ( ( N ` A ) = 0 <-> A = Z ) )

  proof
    cU
    cnv
    wcel
    #
    cA
    cX
    wcel
    #
    wa
    cA
    cN
    cfv
    #
    cc0
    wceq
    #
    cA
    cZ
    wceq
    #
    @0
    @1
    @3
    @4
    wi
    #
    @0
    vx
    cv
    #
    cN
    cfv
    #
    cc0
    wceq
    #
    @6
    cZ
    wceq
    #
    wi
    #
    vy
    cv
    #
    @6
    cU
    cns
    cfv
    #
    co
    cN
    cfv
    @11
    cabs
    cfv
    @7
    cmul
    co
    wceq
    vy
    cc
    wral
    #
    @6
    @11
    cU
    cpv
    cfv
    #
    co
    cN
    cfv
    @7
    @11
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
    @10
    vx
    cX
    wral
    @1
    @5
    wi
    @0
    @14
    @12
    cop
    cvc
    wcel
    cX
    cr
    cN
    wf
    @17
    vx
    vy
    @12
    cU
    @14
    cN
    cX
    cZ
    nvz.1
    @14
    eqid
    @12
    eqid
    nvz.5
    nvz.6
    nvi
    simp3d
    @16
    @10
    vx
    cX
    @10
    @13
    @15
    simp1
    ralimi
    @10
    @5
    vx
    cA
    cX
    @6
    cA
    wceq
    #
    @8
    @3
    @9
    @4
    @18
    @7
    @2
    cc0
    @6
    cA
    cN
    fveq2
    eqeq1d
    @6
    cA
    cZ
    eqeq1
    imbi12d
    rspccv
    3syl
    imp
    @0
    @4
    @3
    wi
    @1
    @0
    @4
    @3
    @4
    @0
    @2
    cZ
    cN
    cfv
    cc0
    cA
    cZ
    cN
    fveq2
    cU
    cN
    cZ
    nvz.5
    nvz.6
    nvz0
    sylan9eqr
    ex
    adantr
    impbid
end
