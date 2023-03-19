include "cnv.mm"
include "wcel.mm"
include "wa.mm"
include "co.mm"
include "cnsb.mm"
include "cfv.mm"
include "wceq.mm"
include "nvzcl.mm"
include "adantr.mm"
include "eqid.mm"
include "imsdval.mm"
include "mpd3an3.mm"
include "c1.mm"
include "cneg.mm"
include "cns.mm"
include "cpv.mm"
include "nvmval.mm"
include "cc.mm"
include "neg1cn.mm"
include "nvsz.mm"
include "mpan2.mm"
include "oveq2d.mm"
include "nv0rid.mm"
include "3eqtrd.mm"
include "fveq2d.mm"
include "eqtr2d.mm"

theorem nvnd
  let cA: class A
  let cD: class D
  let cU: class U
  let cN: class N
  let cX: class X
  let cZ: class Z
  assume nvnd.1: |- X = ( BaseSet ` U )
  assume nvnd.5: |- Z = ( 0vec ` U )
  assume nvnd.6: |- N = ( normCV ` U )
  assume nvnd.8: |- D = ( IndMet ` U )


  assert |- ( ( U e. NrmCVec /\ A e. X ) -> ( N ` A ) = ( A D Z ) )

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
    cA
    cZ
    cD
    co
    #
    cA
    cZ
    cU
    cnsb
    cfv
    #
    co
    #
    cN
    cfv
    #
    cA
    cN
    cfv
    @0
    @1
    cZ
    cX
    wcel
    #
    @3
    @6
    wceq
    @0
    @7
    @1
    cU
    cX
    cZ
    nvnd.1
    nvnd.5
    nvzcl
    adantr
    #
    cA
    cZ
    cD
    cU
    @4
    cN
    cX
    nvnd.1
    @4
    eqid
    #
    nvnd.6
    nvnd.8
    imsdval
    mpd3an3
    @2
    @5
    cA
    cN
    @2
    @5
    cA
    c1
    cneg
    #
    cZ
    cU
    cns
    cfv
    #
    co
    #
    cU
    cpv
    cfv
    #
    co
    #
    cA
    cZ
    @13
    co
    #
    cA
    @0
    @1
    @7
    @5
    @14
    wceq
    @8
    cA
    cZ
    @11
    cU
    @13
    @4
    cX
    nvnd.1
    @13
    eqid
    #
    @11
    eqid
    #
    @9
    nvmval
    mpd3an3
    @0
    @14
    @15
    wceq
    @1
    @0
    @12
    cZ
    cA
    @13
    @0
    @10
    cc
    wcel
    @12
    cZ
    wceq
    neg1cn
    @10
    @11
    cU
    cZ
    @17
    nvnd.5
    nvsz
    mpan2
    oveq2d
    adantr
    cA
    cU
    @13
    cX
    cZ
    nvnd.1
    @16
    nvnd.5
    nv0rid
    3eqtrd
    fveq2d
    eqtr2d
end
