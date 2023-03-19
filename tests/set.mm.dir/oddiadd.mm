include "cvv.mm"
include "wcel.mm"
include "caddc.mm"
include "cplusg.mm"
include "cfv.mm"
include "wceq.mm"
include "cv.mm"
include "c2.mm"
include "cmul.mm"
include "co.mm"
include "c1.mm"
include "cz.mm"
include "wrex.mm"
include "zex.mm"
include "rabex2.mm"
include "cnfldsrngadd.mm"
include "ax-mp.mm"

theorem oddiadd
  let vx: setvar x
  let vz: setvar z
  let cM: class M
  let cO: class O
  let vk: setvar k
  assume oddinmgm.e: |- O = { z e. ZZ | E. x e. ZZ z = ( ( 2 x. x ) + 1 ) }
  assume oddinmgm.r: |- M = ( CCfld |`s O )

  disjoint x z
  disjoint k x
  assert |- + = ( +g ` M )

  proof
    cO
    cvv
    wcel
    caddc
    cM
    cplusg
    cfv
    wceq
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
    vz
    cz
    cO
    oddinmgm.e
    zex
    rabex2
    cM
    cO
    cvv
    oddinmgm.r
    cnfldsrngadd
    ax-mp
end
