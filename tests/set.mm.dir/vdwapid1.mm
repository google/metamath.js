include "cn.mm"
include "wcel.mm"
include "w3a.mm"
include "csn.mm"
include "caddc.mm"
include "co.mm"
include "c1.mm"
include "cmin.mm"
include "cvdwa.mm"
include "cfv.mm"
include "cun.mm"
include "wss.mm"
include "ssun1.mm"
include "wb.mm"
include "snssg.mm"
include "3ad2ant2.mm"
include "mpbiri.mm"
include "cc.mm"
include "wceq.mm"
include "nncn.mm"
include "3ad2ant1.mm"
include "ax-1cn.mm"
include "npcan.mm"
include "sylancl.mm"
include "fveq2d.mm"
include "oveqd.mm"
include "cn0.mm"
include "nnm1nn0.mm"
include "vdwapun.mm"
include "syl3an1.mm"
include "eqtr3d.mm"
include "eleqtrrd.mm"

theorem vdwapid1
  let cA: class A
  let cD: class D
  let cK: class K
  let va: setvar a
  let vd: setvar d
  let vm: setvar m
  let vn: setvar n
  let vx: setvar x
  let vk: setvar k
  let cX: class X


  assert |- ( ( K e. NN /\ A e. NN /\ D e. NN ) -> A e. ( A ( AP ` K ) D ) )

  proof
    cK
    cn
    wcel
    #
    cA
    cn
    wcel
    #
    cD
    cn
    wcel
    #
    w3a
    #
    cA
    cA
    csn
    #
    cA
    cD
    caddc
    co
    cD
    cK
    c1
    cmin
    co
    #
    cvdwa
    cfv
    co
    #
    cun
    #
    cA
    cD
    cK
    cvdwa
    cfv
    #
    co
    #
    @3
    cA
    @7
    wcel
    #
    @4
    @7
    wss
    #
    @4
    @6
    ssun1
    @1
    @0
    @10
    @11
    wb
    @2
    cA
    @7
    cn
    snssg
    3ad2ant2
    mpbiri
    @3
    cA
    cD
    @5
    c1
    caddc
    co
    #
    cvdwa
    cfv
    #
    co
    #
    @9
    @7
    @3
    @13
    @8
    cA
    cD
    @3
    @12
    cK
    cvdwa
    @3
    cK
    cc
    wcel
    #
    c1
    cc
    wcel
    @12
    cK
    wceq
    @0
    @1
    @15
    @2
    cK
    nncn
    3ad2ant1
    ax-1cn
    cK
    c1
    npcan
    sylancl
    fveq2d
    oveqd
    @0
    @5
    cn0
    wcel
    @1
    @2
    @14
    @7
    wceq
    cK
    nnm1nn0
    cA
    cD
    @5
    vdwapun
    syl3an1
    eqtr3d
    eleqtrrd
end
