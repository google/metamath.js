include "crng.mm"
include "wcel.mm"
include "cabl.mm"
include "csgrp.mm"
include "cv.mm"
include "caddc.mm"
include "co.mm"
include "cmul.mm"
include "wceq.mm"
include "wa.mm"
include "wral.mm"
include "2zrngaabl.mm"
include "2zrngmsgrp.mm"
include "cc.mm"
include "c2.mm"
include "cz.mm"
include "wrex.mm"
include "crab.mm"
include "elrabi.mm"
include "zcnd.mm"
include "eleq2s.mm"
include "w3a.mm"
include "adddi.mm"
include "adddir.mm"
include "jca.mm"
include "syl3an.mm"
include "rgen3.mm"
include "2zrngbas.mm"
include "2zrngadd.mm"
include "2zrngmul.mm"
include "isrng.mm"
include "mpbir3an.mm"

theorem 2zrngALT
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
  assert |- R e. Rng

  proof
    cR
    crng
    wcel
    cR
    cabl
    wcel
    cM
    csgrp
    wcel
    va
    cv
    #
    vb
    cv
    #
    vy
    cv
    #
    caddc
    co
    cmul
    co
    @0
    @1
    cmul
    co
    @0
    @2
    cmul
    co
    #
    caddc
    co
    wceq
    #
    @0
    @1
    caddc
    co
    @2
    cmul
    co
    @3
    @1
    @2
    cmul
    co
    caddc
    co
    wceq
    #
    wa
    #
    vy
    cE
    wral
    vb
    cE
    wral
    va
    cE
    wral
    vx
    vz
    cR
    cE
    2zrng.e
    2zrngbas.r
    2zrngaabl
    vx
    vz
    cR
    cE
    cM
    2zrng.e
    2zrngbas.r
    2zrngmmgm.1
    2zrngmsgrp
    @6
    va
    vb
    vy
    cE
    cE
    cE
    @0
    cE
    wcel
    @0
    cc
    wcel
    #
    @1
    cE
    wcel
    @1
    cc
    wcel
    #
    @2
    cE
    wcel
    @2
    cc
    wcel
    #
    @6
    @7
    @0
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
    cE
    @0
    @11
    wcel
    @0
    @10
    vz
    @0
    cz
    elrabi
    zcnd
    2zrng.e
    eleq2s
    @8
    @1
    @11
    cE
    @1
    @11
    wcel
    @1
    @10
    vz
    @1
    cz
    elrabi
    zcnd
    2zrng.e
    eleq2s
    @9
    @2
    @11
    cE
    @2
    @11
    wcel
    @2
    @10
    vz
    @2
    cz
    elrabi
    zcnd
    2zrng.e
    eleq2s
    @7
    @8
    @9
    w3a
    @4
    @5
    @0
    @1
    @2
    adddi
    @0
    @1
    @2
    adddir
    jca
    syl3an
    rgen3
    va
    vb
    vy
    cE
    caddc
    cR
    cmul
    cM
    vx
    vz
    cR
    cE
    2zrng.e
    2zrngbas.r
    2zrngbas
    2zrngmmgm.1
    vx
    vz
    cR
    cE
    2zrng.e
    2zrngbas.r
    2zrngadd
    vx
    vz
    cR
    cE
    2zrng.e
    2zrngbas.r
    2zrngmul
    isrng
    mpbir3an
end
