include "cabl.mm"
include "wcel.mm"
include "cgrp.mm"
include "ccmn.mm"
include "wa.mm"
include "2zrngagrp.mm"
include "2zrngacmnd.mm"
include "pm3.2i.mm"
include "isabl.mm"
include "mpbir.mm"

theorem 2zrngaabl
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
  assert |- R e. Abel

  proof
    cR
    cabl
    wcel
    cR
    cgrp
    wcel
    #
    cR
    ccmn
    wcel
    #
    wa
    @0
    @1
    vx
    vz
    cR
    cE
    2zrng.e
    2zrngbas.r
    2zrngagrp
    vx
    vz
    cR
    cE
    2zrng.e
    2zrngbas.r
    2zrngacmnd
    pm3.2i
    cR
    isabl
    mpbir
end
