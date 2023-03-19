include "cn.mm"
include "wcel.mm"
include "cv.mm"
include "cdiv.mm"
include "co.mm"
include "wa.mm"
include "cdvds.mm"
include "wbr.mm"
include "crab.mm"
include "eleq2i.mm"
include "dvdsdivcl.mm"
include "sylan2b.mm"
include "syl6eleqr.mm"
include "wceq.mm"
include "wb.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "sseli.mm"
include "anim12i.mm"
include "cmul.mm"
include "cc.mm"
include "nncn.mm"
include "adantr.mm"
include "ad2antrl.mm"
include "ad2antll.mm"
include "cc0.mm"
include "wne.mm"
include "nnne0.mm"
include "divmul3d.mm"
include "divmul2d.mm"
include "bitr4d.mm"
include "sylan2.mm"
include "eqcom.mm"
include "3bitr4g.mm"
include "f1o2d.mm"

theorem dvdsflip
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cF: class F
  let cN: class N
  let vz: setvar z
  assume dvdsflip.a: |- A = { x e. NN | x || N }
  assume dvdsflip.f: |- F = ( y e. A |-> ( N / y ) )

  disjoint A y
  disjoint x y
  disjoint N x
  disjoint N y
  disjoint y z
  disjoint A z
  disjoint x z
  disjoint N z
  assert |- ( N e. NN -> F : A -1-1-onto-> A )

  proof
    cN
    cn
    wcel
    #
    vy
    vz
    cA
    cA
    cN
    vy
    cv
    #
    cdiv
    co
    #
    cN
    vz
    cv
    #
    cdiv
    co
    #
    cF
    dvdsflip.f
    @0
    @1
    cA
    wcel
    #
    wa
    @2
    vx
    cv
    cN
    cdvds
    wbr
    #
    vx
    cn
    crab
    #
    cA
    @5
    @0
    @1
    @7
    wcel
    @2
    @7
    wcel
    cA
    @7
    @1
    dvdsflip.a
    eleq2i
    vx
    @1
    cN
    dvdsdivcl
    sylan2b
    dvdsflip.a
    syl6eleqr
    @0
    @3
    cA
    wcel
    #
    wa
    @4
    @7
    cA
    @8
    @0
    @3
    @7
    wcel
    @4
    @7
    wcel
    cA
    @7
    @3
    dvdsflip.a
    eleq2i
    vx
    @3
    cN
    dvdsdivcl
    sylan2b
    dvdsflip.a
    syl6eleqr
    @0
    @5
    @8
    wa
    #
    wa
    @4
    @1
    wceq
    #
    @2
    @3
    wceq
    #
    @1
    @4
    wceq
    @3
    @2
    wceq
    @9
    @0
    @1
    cn
    wcel
    #
    @3
    cn
    wcel
    #
    wa
    #
    @10
    @11
    wb
    @5
    @12
    @8
    @13
    cA
    cn
    @1
    cA
    @7
    cn
    dvdsflip.a
    @6
    vx
    cn
    ssrab2
    eqsstri
    #
    sseli
    cA
    cn
    @3
    @15
    sseli
    anim12i
    @0
    @14
    wa
    #
    @10
    cN
    @1
    @3
    cmul
    co
    wceq
    @11
    @16
    cN
    @1
    @3
    @0
    cN
    cc
    wcel
    @14
    cN
    nncn
    adantr
    #
    @12
    @1
    cc
    wcel
    @0
    @13
    @1
    nncn
    ad2antrl
    #
    @13
    @3
    cc
    wcel
    @0
    @12
    @3
    nncn
    ad2antll
    #
    @13
    @3
    cc0
    wne
    @0
    @12
    @3
    nnne0
    ad2antll
    divmul3d
    @16
    cN
    @3
    @1
    @17
    @19
    @18
    @12
    @1
    cc0
    wne
    @0
    @13
    @1
    nnne0
    ad2antrl
    divmul2d
    bitr4d
    sylan2
    @1
    @4
    eqcom
    @3
    @2
    eqcom
    3bitr4g
    f1o2d
end
