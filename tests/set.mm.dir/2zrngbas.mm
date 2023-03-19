include "cc.mm"
include "wss.mm"
include "cbs.mm"
include "cfv.mm"
include "wceq.mm"
include "cv.mm"
include "c2.mm"
include "cmul.mm"
include "co.mm"
include "cz.mm"
include "wrex.mm"
include "crab.mm"
include "ssrab2.mm"
include "zsscn.mm"
include "sstri.mm"
include "eqsstri.mm"
include "cnfldsrngbas.mm"
include "ax-mp.mm"

theorem 2zrngbas
  let vx: setvar x
  let vz: setvar z
  let cR: class R
  let cE: class E
  let vk: setvar k
  assume 2zrng.e: |- E = { z e. ZZ | E. x e. ZZ z = ( 2 x. x ) }
  assume 2zrngbas.r: |- R = ( CCfld |`s E )

  disjoint x z
  disjoint k x
  assert |- E = ( Base ` R )

  proof
    cE
    cc
    wss
    cE
    cR
    cbs
    cfv
    wceq
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
    #
    cc
    2zrng.e
    @1
    cz
    cc
    @0
    vz
    cz
    ssrab2
    zsscn
    sstri
    eqsstri
    cR
    cE
    2zrngbas.r
    cnfldsrngbas
    ax-mp
end
