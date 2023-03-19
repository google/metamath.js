include "csgrp.mm"
include "wcel.mm"
include "cmgm.mm"
include "cv.mm"
include "cmul.mm"
include "co.mm"
include "wceq.mm"
include "c2.mm"
include "cz.mm"
include "wrex.mm"
include "crab.mm"
include "wral.mm"
include "2zrngmmgm.mm"
include "w3a.mm"
include "cc.mm"
include "elrabi.mm"
include "3anim123i.mm"
include "zcn.mm"
include "mulass.mm"
include "3syl.mm"
include "rgen3.mm"
include "cbs.mm"
include "cfv.mm"
include "2zrngbas.mm"
include "mgpbas.mm"
include "eqtr3i.mm"
include "2zrngmul.mm"
include "mgpplusg.mm"
include "issgrp.mm"
include "mpbir2an.mm"

theorem 2zrngmsgrp
  let vx: setvar x
  let vz: setvar z
  let cR: class R
  let cE: class E
  let cM: class M
  let va: setvar a
  let vb: setvar b
  let vy: setvar y
  let vk: setvar k
  assume 2zrng.e: |- E = { z e. ZZ | E. x e. ZZ z = ( 2 x. x ) }
  assume 2zrngbas.r: |- R = ( CCfld |`s E )
  assume 2zrngmmgm.1: |- M = ( mulGrp ` R )

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
  disjoint M a
  disjoint M b
  disjoint M y
  disjoint k x
  assert |- M e. SGrp

  proof
    cM
    csgrp
    wcel
    cM
    cmgm
    wcel
    va
    cv
    #
    vy
    cv
    #
    cmul
    co
    vb
    cv
    #
    cmul
    co
    @0
    @1
    @2
    cmul
    co
    cmul
    co
    wceq
    #
    vb
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
    wral
    vy
    @5
    wral
    va
    @5
    wral
    vx
    vz
    cR
    cE
    cM
    2zrng.e
    2zrngbas.r
    2zrngmmgm.1
    2zrngmmgm
    @3
    va
    vy
    vb
    @5
    @5
    @5
    @0
    @5
    wcel
    #
    @1
    @5
    wcel
    #
    @2
    @5
    wcel
    #
    w3a
    @0
    cz
    wcel
    #
    @1
    cz
    wcel
    #
    @2
    cz
    wcel
    #
    w3a
    @0
    cc
    wcel
    #
    @1
    cc
    wcel
    #
    @2
    cc
    wcel
    #
    w3a
    @3
    @6
    @9
    @7
    @10
    @8
    @11
    @4
    vz
    @0
    cz
    elrabi
    @4
    vz
    @1
    cz
    elrabi
    @4
    vz
    @2
    cz
    elrabi
    3anim123i
    @9
    @12
    @10
    @13
    @11
    @14
    @0
    zcn
    @1
    zcn
    @2
    zcn
    3anim123i
    @0
    @1
    @2
    mulass
    3syl
    rgen3
    va
    vy
    vb
    @5
    cM
    cmul
    cE
    @5
    cM
    cbs
    cfv
    2zrng.e
    cE
    cR
    cM
    2zrngmmgm.1
    vx
    vz
    cR
    cE
    2zrng.e
    2zrngbas.r
    2zrngbas
    mgpbas
    eqtr3i
    cR
    cmul
    cM
    2zrngmmgm.1
    vx
    vz
    cR
    cE
    2zrng.e
    2zrngbas.r
    2zrngmul
    mgpplusg
    issgrp
    mpbir2an
end
