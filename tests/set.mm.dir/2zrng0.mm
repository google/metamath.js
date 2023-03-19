include "ccnfld.mm"
include "cmnd.mm"
include "wcel.mm"
include "cc0.mm"
include "cc.mm"
include "wss.mm"
include "c0g.mm"
include "cfv.mm"
include "wceq.mm"
include "ccrg.mm"
include "crg.mm"
include "cncrng.mm"
include "crngring.mm"
include "ringmnd.mm"
include "mp2b.mm"
include "0even.mm"
include "cz.mm"
include "cv.mm"
include "c2.mm"
include "cmul.mm"
include "co.mm"
include "wrex.mm"
include "crab.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "zsscn.mm"
include "sstri.mm"
include "cnfldbas.mm"
include "cnfld0.mm"
include "ress0g.mm"
include "mp3an.mm"

theorem 2zrng0
  let vx: setvar x
  let vz: setvar z
  let cR: class R
  let cE: class E
  let vk: setvar k
  assume 2zrng.e: |- E = { z e. ZZ | E. x e. ZZ z = ( 2 x. x ) }
  assume 2zrngbas.r: |- R = ( CCfld |`s E )

  disjoint x z
  disjoint k x
  assert |- 0 = ( 0g ` R )

  proof
    ccnfld
    cmnd
    wcel
    #
    cc0
    cE
    wcel
    cE
    cc
    wss
    cc0
    cR
    c0g
    cfv
    wceq
    ccnfld
    ccrg
    wcel
    ccnfld
    crg
    wcel
    @0
    cncrng
    ccnfld
    crngring
    ccnfld
    ringmnd
    mp2b
    vx
    vz
    cE
    2zrng.e
    0even
    cE
    cz
    cc
    cE
    vz
    cv
    c2
    vx
    cv
    cmul
    co
    wceq
    vx
    cz
    wrex
    #
    vz
    cz
    crab
    cz
    2zrng.e
    @1
    vz
    cz
    ssrab2
    eqsstri
    zsscn
    sstri
    cE
    cc
    ccnfld
    cR
    cc0
    2zrngbas.r
    cnfldbas
    cnfld0
    ress0g
    mp3an
end
