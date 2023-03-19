include "cnv.mm"
include "wcel.mm"
include "wa.mm"
include "c1.mm"
include "cneg.mm"
include "co.mm"
include "cpv.mm"
include "cfv.mm"
include "cgn.mm"
include "wceq.mm"
include "cc.mm"
include "neg1cn.mm"
include "nvscl.mm"
include "mp3an2.mm"
include "eqid.mm"
include "nvinv.mm"
include "syldan.mm"
include "fveq2d.mm"
include "cgr.mm"
include "nvgrp.mm"
include "bafval.mm"
include "grpo2inv.mm"
include "sylan.mm"
include "3eqtrd.mm"

theorem nvnegneg
  let cA: class A
  let cS: class S
  let cU: class U
  let cX: class X
  assume nvnegneg.1: |- X = ( BaseSet ` U )
  assume nvnegneg.4: |- S = ( .sOLD ` U )


  assert |- ( ( U e. NrmCVec /\ A e. X ) -> ( -u 1 S ( -u 1 S A ) ) = A )

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
    #
    c1
    cneg
    #
    @3
    cA
    cS
    co
    #
    cS
    co
    #
    @4
    cU
    cpv
    cfv
    #
    cgn
    cfv
    #
    cfv
    #
    cA
    @7
    cfv
    #
    @7
    cfv
    #
    cA
    @0
    @1
    @4
    cX
    wcel
    #
    @5
    @8
    wceq
    @0
    @3
    cc
    wcel
    @1
    @11
    neg1cn
    @3
    cA
    cS
    cU
    cX
    nvnegneg.1
    nvnegneg.4
    nvscl
    mp3an2
    @4
    cS
    cU
    @6
    @7
    cX
    nvnegneg.1
    @6
    eqid
    #
    nvnegneg.4
    @7
    eqid
    #
    nvinv
    syldan
    @2
    @4
    @9
    @7
    cA
    cS
    cU
    @6
    @7
    cX
    nvnegneg.1
    @12
    nvnegneg.4
    @13
    nvinv
    fveq2d
    @0
    @6
    cgr
    wcel
    @1
    @10
    cA
    wceq
    cU
    @6
    @12
    nvgrp
    cA
    @6
    @7
    cX
    cU
    @6
    cX
    nvnegneg.1
    @12
    bafval
    @13
    grpo2inv
    sylan
    3eqtrd
end
