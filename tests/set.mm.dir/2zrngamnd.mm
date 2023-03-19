include "cmnd.mm"
include "wcel.mm"
include "csgrp.mm"
include "cv.mm"
include "caddc.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "wral.mm"
include "wrex.mm"
include "2zrngasgrp.mm"
include "cc0.mm"
include "0even.mm"
include "id.mm"
include "wb.mm"
include "oveq1.mm"
include "eqeq1d.mm"
include "oveq2.mm"
include "anbi12d.mm"
include "ralbidv.mm"
include "adantl.mm"
include "cc.mm"
include "cz.mm"
include "c2.mm"
include "cmul.mm"
include "crab.mm"
include "elrabi.mm"
include "eleq2s.mm"
include "zcnd.mm"
include "addid2.mm"
include "addid1.mm"
include "jca.mm"
include "syl.mm"
include "ralrimiva.mm"
include "rspcedvd.mm"
include "ax-mp.mm"
include "2zrngbas.mm"
include "2zrngadd.mm"
include "ismnddef.mm"
include "mpbir2an.mm"

theorem 2zrngamnd
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
  assert |- R e. Mnd

  proof
    cR
    cmnd
    wcel
    cR
    csgrp
    wcel
    vx
    cv
    #
    vy
    cv
    #
    caddc
    co
    #
    @1
    wceq
    #
    @1
    @0
    caddc
    co
    #
    @1
    wceq
    #
    wa
    #
    vy
    cE
    wral
    #
    vx
    cE
    wrex
    #
    vx
    vz
    cR
    cE
    2zrng.e
    2zrngbas.r
    2zrngasgrp
    cc0
    cE
    wcel
    #
    @8
    vx
    vz
    cE
    2zrng.e
    0even
    @9
    @7
    cc0
    @1
    caddc
    co
    #
    @1
    wceq
    #
    @1
    cc0
    caddc
    co
    #
    @1
    wceq
    #
    wa
    #
    vy
    cE
    wral
    #
    vx
    cc0
    cE
    @9
    id
    @0
    cc0
    wceq
    #
    @7
    @15
    wb
    @9
    @16
    @6
    @14
    vy
    cE
    @16
    @3
    @11
    @5
    @13
    @16
    @2
    @10
    @1
    @0
    cc0
    @1
    caddc
    oveq1
    eqeq1d
    @16
    @4
    @12
    @1
    @0
    cc0
    @1
    caddc
    oveq2
    eqeq1d
    anbi12d
    ralbidv
    adantl
    @9
    @14
    vy
    cE
    @1
    cE
    wcel
    #
    @14
    @9
    @17
    @1
    cc
    wcel
    #
    @14
    @17
    @1
    @1
    cz
    wcel
    @1
    vz
    cv
    c2
    @0
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
    cE
    @19
    vz
    @1
    cz
    elrabi
    2zrng.e
    eleq2s
    zcnd
    @18
    @11
    @13
    @1
    addid2
    @1
    addid1
    jca
    syl
    adantl
    ralrimiva
    rspcedvd
    ax-mp
    cE
    caddc
    vx
    cR
    vy
    vx
    vz
    cR
    cE
    2zrng.e
    2zrngbas.r
    2zrngbas
    vx
    vz
    cR
    cE
    2zrng.e
    2zrngbas.r
    2zrngadd
    ismnddef
    mpbir2an
end
