include "cwrecs.mm"
include "cv.mm"
include "wfn.mm"
include "wss.mm"
include "cpred.mm"
include "wral.mm"
include "wa.mm"
include "cfv.mm"
include "cres.mm"
include "wceq.mm"
include "w3a.mm"
include "wex.mm"
include "cab.mm"
include "cuni.mm"
include "df-wrecs.mm"
include "nfv.mm"
include "nfcv.mm"
include "nfss.mm"
include "nfpred.mm"
include "nfral.mm"
include "nfan.mm"
include "nfres.mm"
include "nffv.mm"
include "nfeq2.mm"
include "nf3an.mm"
include "nfex.mm"
include "nfab.mm"
include "nfuni.mm"
include "nfcxfr.mm"

theorem nfwrecs
  let vx: setvar x
  let cA: class A
  let cR: class R
  let cF: class F
  let vf: setvar f
  let vy: setvar y
  let vz: setvar z
  assume nfwrecs.1: |- F/_ x R
  assume nfwrecs.2: |- F/_ x A
  assume nfwrecs.3: |- F/_ x F


  assert |- F/_ x wrecs ( R , A , F )

  proof
    vx
    cA
    cR
    cF
    cwrecs
    vf
    cv
    #
    vy
    cv
    #
    wfn
    #
    @1
    cA
    wss
    #
    cA
    cR
    vz
    cv
    #
    cpred
    #
    @1
    wss
    #
    vz
    @1
    wral
    #
    wa
    #
    @4
    @0
    cfv
    #
    @0
    @5
    cres
    #
    cF
    cfv
    #
    wceq
    #
    vz
    @1
    wral
    #
    w3a
    #
    vy
    wex
    #
    vf
    cab
    #
    cuni
    vy
    vz
    cA
    cR
    vf
    cF
    df-wrecs
    vx
    @16
    @15
    vx
    vf
    @14
    vx
    vy
    @2
    @8
    @13
    vx
    @2
    vx
    nfv
    @3
    @7
    vx
    vx
    @1
    cA
    vx
    @1
    nfcv
    #
    nfwrecs.2
    nfss
    @6
    vx
    vz
    @1
    @17
    vx
    @5
    @1
    vx
    cA
    cR
    @4
    nfwrecs.1
    nfwrecs.2
    vx
    @4
    nfcv
    nfpred
    #
    @17
    nfss
    nfral
    nfan
    @12
    vx
    vz
    @1
    @17
    vx
    @9
    @11
    vx
    @10
    cF
    nfwrecs.3
    vx
    @0
    @5
    vx
    @0
    nfcv
    @18
    nfres
    nffv
    nfeq2
    nfral
    nf3an
    nfex
    nfab
    nfuni
    nfcxfr
end
