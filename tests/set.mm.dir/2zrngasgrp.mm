include "csgrp.mm"
include "wcel.mm"
include "cmgm.mm"
include "cv.mm"
include "caddc.mm"
include "co.mm"
include "wceq.mm"
include "c2.mm"
include "cmul.mm"
include "cz.mm"
include "wrex.mm"
include "crab.mm"
include "wral.mm"
include "2zrngamgm.mm"
include "w3a.mm"
include "cc.mm"
include "elrabi.mm"
include "3anim123i.mm"
include "zcn.mm"
include "addass.mm"
include "3syl.mm"
include "rgen3.mm"
include "cbs.mm"
include "cfv.mm"
include "2zrngbas.mm"
include "eqtr3i.mm"
include "2zrngadd.mm"
include "issgrp.mm"
include "mpbir2an.mm"

theorem 2zrngasgrp
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
  disjoint k x
  assert |- R e. SGrp

  proof
    cR
    csgrp
    wcel
    cR
    cmgm
    wcel
    va
    cv
    #
    vy
    cv
    #
    caddc
    co
    vb
    cv
    #
    caddc
    co
    @0
    @1
    @2
    caddc
    co
    caddc
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
    2zrng.e
    2zrngbas.r
    2zrngamgm
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
    addass
    3syl
    rgen3
    va
    vy
    vb
    @5
    cR
    caddc
    cE
    @5
    cR
    cbs
    cfv
    2zrng.e
    vx
    vz
    cR
    cE
    2zrng.e
    2zrngbas.r
    2zrngbas
    eqtr3i
    vx
    vz
    cR
    cE
    2zrng.e
    2zrngbas.r
    2zrngadd
    issgrp
    mpbir2an
end
