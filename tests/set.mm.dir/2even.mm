include "c2.mm"
include "cv.mm"
include "cmul.mm"
include "co.mm"
include "wceq.mm"
include "cz.mm"
include "wrex.mm"
include "crab.mm"
include "wcel.mm"
include "2z.mm"
include "cc.mm"
include "2cn.mm"
include "c1.mm"
include "1zzd.mm"
include "wb.mm"
include "oveq2.mm"
include "eqeq2d.mm"
include "adantl.mm"
include "mulid1.mm"
include "eqcomd.mm"
include "rspcedvd.mm"
include "ax-mp.mm"
include "eqeq1.mm"
include "rexbidv.mm"
include "elrab.mm"
include "mpbir2an.mm"
include "eleqtrri.mm"

theorem 2even
  let vx: setvar x
  let vz: setvar z
  let cE: class E
  let vk: setvar k
  assume 2zrng.e: |- E = { z e. ZZ | E. x e. ZZ z = ( 2 x. x ) }

  disjoint x z
  disjoint k x
  assert |- 2 e. E

  proof
    c2
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
    c2
    @5
    wcel
    c2
    cz
    wcel
    c2
    @2
    wceq
    #
    vx
    cz
    wrex
    #
    2z
    c2
    cc
    wcel
    #
    @7
    2cn
    @8
    @6
    c2
    c2
    c1
    cmul
    co
    #
    wceq
    #
    vx
    c1
    cz
    @8
    1zzd
    @1
    c1
    wceq
    #
    @6
    @10
    wb
    @8
    @11
    @2
    @9
    c2
    @1
    c1
    c2
    cmul
    oveq2
    eqeq2d
    adantl
    @8
    @9
    c2
    c2
    mulid1
    eqcomd
    rspcedvd
    ax-mp
    @4
    @7
    vz
    c2
    cz
    @0
    c2
    wceq
    @3
    @6
    vx
    cz
    @0
    c2
    @2
    eqeq1
    rexbidv
    elrab
    mpbir2an
    2zrng.e
    eleqtrri
end
