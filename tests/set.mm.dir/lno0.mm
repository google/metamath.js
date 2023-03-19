include "cnv.mm"
include "wcel.mm"
include "w3a.mm"
include "c1.mm"
include "cneg.mm"
include "cns.mm"
include "cfv.mm"
include "co.mm"
include "cpv.mm"
include "cc.mm"
include "wceq.mm"
include "neg1cn.mm"
include "a1i.mm"
include "nvzcl.mm"
include "3ad2ant1.mm"
include "3jca.mm"
include "eqid.mm"
include "lnolin.mm"
include "mpdan.mm"
include "nvlinv.mm"
include "fveq2d.mm"
include "simp2.mm"
include "lnof.mm"
include "ffvelrnd.mm"
include "syl2anc.mm"
include "3eqtr3d.mm"

theorem lno0
  let cQ: class Q
  let cT: class T
  let cU: class U
  let cL: class L
  let cW: class W
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume lno0.1: |- X = ( BaseSet ` U )
  assume lno0.2: |- Y = ( BaseSet ` W )
  assume lno0.5: |- Q = ( 0vec ` U )
  assume lno0.z: |- Z = ( 0vec ` W )
  assume lno0.7: |- L = ( U LnOp W )


  assert |- ( ( U e. NrmCVec /\ W e. NrmCVec /\ T e. L ) -> ( T ` Q ) = Z )

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
    c1
    cneg
    #
    cQ
    cU
    cns
    cfv
    #
    co
    cQ
    cU
    cpv
    cfv
    #
    co
    #
    cT
    cfv
    #
    @4
    cQ
    cT
    cfv
    #
    cW
    cns
    cfv
    #
    co
    @9
    cW
    cpv
    cfv
    #
    co
    #
    @9
    cZ
    @3
    @4
    cc
    wcel
    #
    cQ
    cX
    wcel
    #
    @14
    w3a
    @8
    @12
    wceq
    @3
    @13
    @14
    @14
    @13
    @3
    neg1cn
    a1i
    @0
    @1
    @14
    @2
    cU
    cX
    cQ
    lno0.1
    lno0.5
    nvzcl
    #
    3ad2ant1
    #
    @16
    3jca
    @4
    cQ
    cQ
    @5
    @10
    cT
    cU
    @6
    @11
    cL
    cW
    cX
    cY
    lno0.1
    lno0.2
    @6
    eqid
    #
    @11
    eqid
    #
    @5
    eqid
    #
    @10
    eqid
    #
    lno0.7
    lnolin
    mpdan
    @0
    @1
    @8
    @9
    wceq
    @2
    @0
    @7
    cQ
    cT
    @0
    @14
    @7
    cQ
    wceq
    @15
    cQ
    @5
    cU
    @6
    cX
    cQ
    lno0.1
    @17
    @19
    lno0.5
    nvlinv
    mpdan
    fveq2d
    3ad2ant1
    @3
    @1
    @9
    cY
    wcel
    @12
    cZ
    wceq
    @0
    @1
    @2
    simp2
    @3
    cX
    cY
    cQ
    cT
    cT
    cU
    cL
    cW
    cX
    cY
    lno0.1
    lno0.2
    lno0.7
    lnof
    @16
    ffvelrnd
    @9
    @10
    cW
    @11
    cY
    cZ
    lno0.2
    @18
    @20
    lno0.z
    nvlinv
    syl2anc
    3eqtr3d
end
