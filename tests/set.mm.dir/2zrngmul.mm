include "cvv.mm"
include "wcel.mm"
include "cmul.mm"
include "cmulr.mm"
include "cfv.mm"
include "wceq.mm"
include "cv.mm"
include "c2.mm"
include "co.mm"
include "cz.mm"
include "wrex.mm"
include "zex.mm"
include "rabex2.mm"
include "cnfldsrngmul.mm"
include "ax-mp.mm"

theorem 2zrngmul
  let vx: setvar x
  let vz: setvar z
  let cR: class R
  let cE: class E
  let va: setvar a
  let vb: setvar b
  let vy: setvar y
  let vk: setvar k
  assume 2zrng.e: |- E = { z e. ZZ | E. x e. ZZ z = ( 2 x. x ) }
  assume 2zrngbas.r: |- R = ( CCfld |`s E )

  disjoint x z
  disjoint R x
  disjoint R z
  disjoint E x
  disjoint E z
  disjoint E a
  disjoint E b
  disjoint a b
  disjoint R a
  disjoint R b
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint x y
  disjoint y z
  disjoint R y
  disjoint E y
  disjoint k x
  assert |- x. = ( .r ` R )

  proof
    cE
    cvv
    wcel
    cmul
    cR
    cmulr
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
    cnfldsrngmul
    ax-mp
end
