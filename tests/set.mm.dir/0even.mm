include "cc0.mm"
include "cv.mm"
include "c2.mm"
include "cmul.mm"
include "co.mm"
include "wceq.mm"
include "cz.mm"
include "wrex.mm"
include "crab.mm"
include "wcel.mm"
include "0z.mm"
include "cc.mm"
include "2cn.mm"
include "0zd.mm"
include "wb.mm"
include "oveq2.mm"
include "eqeq2d.mm"
include "adantl.mm"
include "mul01.mm"
include "eqcomd.mm"
include "rspcedvd.mm"
include "ax-mp.mm"
include "eqeq1.mm"
include "rexbidv.mm"
include "elrab.mm"
include "mpbir2an.mm"
include "eleqtrri.mm"

theorem 0even
  let vx: setvar x
  let vz: setvar z
  let cE: class E
  let vk: setvar k
  assume 2zrng.e: |- E = { z e. ZZ | E. x e. ZZ z = ( 2 x. x ) }

  disjoint x z
  disjoint k x
  assert |- 0 e. E

  proof
    cc0
    vz
    cv
    #
    c2
    vx
    cv
    #
    cmul
    co
    #
    wceq
    #
    vx
    cz
    wrex
    #
    vz
    cz
    crab
    #
    cE
    cc0
    @5
    wcel
    cc0
    cz
    wcel
    cc0
    @2
    wceq
    #
    vx
    cz
    wrex
    #
    0z
    c2
    cc
    wcel
    #
    @7
    2cn
    @8
    @6
    cc0
    c2
    cc0
    cmul
    co
    #
    wceq
    #
    vx
    cc0
    cz
    @8
    0zd
    @1
    cc0
    wceq
    #
    @6
    @10
    wb
    @8
    @11
    @2
    @9
    cc0
    @1
    cc0
    c2
    cmul
    oveq2
    eqeq2d
    adantl
    @8
    @9
    cc0
    c2
    mul01
    eqcomd
    rspcedvd
    ax-mp
    @4
    @7
    vz
    cc0
    cz
    @0
    cc0
    wceq
    @3
    @6
    vx
    cz
    @0
    cc0
    @2
    eqeq1
    rexbidv
    elrab
    mpbir2an
    2zrng.e
    eleqtrri
end
