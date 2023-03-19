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
include "cz.mm"
include "wrex.mm"
include "zex.mm"
include "rabex2.mm"
include "cnfldsrngadd.mm"
include "ax-mp.mm"

theorem 2zrngadd
  let vx: setvar x
  let vz: setvar z
  let cR: class R
  let cE: class E
  let vk: setvar k
  assume 2zrng.e: |- E = { z e. ZZ | E. x e. ZZ z = ( 2 x. x ) }
  assume 2zrngbas.r: |- R = ( CCfld |`s E )

  disjoint x z
  disjoint k x
  assert |- + = ( +g ` R )

  proof
    cE
    cvv
    wcel
    caddc
    cR
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
    wceq
    vx
    cz
    wrex
    vz
    cz
    cE
    2zrng.e
    zex
    rabex2
    cR
    cE
    cvv
    2zrngbas.r
    cnfldsrngadd
    ax-mp
end
