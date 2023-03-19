include "cc.mm"
include "wss.mm"
include "cbs.mm"
include "cfv.mm"
include "wceq.mm"
include "cz.mm"
include "cv.mm"
include "c2.mm"
include "cmul.mm"
include "co.mm"
include "c1.mm"
include "caddc.mm"
include "wrex.mm"
include "crab.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "zsscn.mm"
include "sstri.mm"
include "cnfldsrngbas.mm"
include "ax-mp.mm"

theorem oddibas
  let vx: setvar x
  let vz: setvar z
  let cM: class M
  let cO: class O
  let vk: setvar k
  assume oddinmgm.e: |- O = { z e. ZZ | E. x e. ZZ z = ( ( 2 x. x ) + 1 ) }
  assume oddinmgm.r: |- M = ( CCfld |`s O )

  disjoint x z
  disjoint k x
  assert |- O = ( Base ` M )

  proof
    cO
    cc
    wss
    cO
    cM
    cbs
    cfv
    wceq
    cO
    cz
    cc
    cO
    vz
    cv
    c2
    vx
    cv
    cmul
    co
    c1
    caddc
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
    oddinmgm.e
    @0
    vz
    cz
    ssrab2
    eqsstri
    zsscn
    sstri
    cM
    cO
    oddinmgm.r
    cnfldsrngbas
    ax-mp
end
