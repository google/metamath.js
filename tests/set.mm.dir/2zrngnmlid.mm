include "cv.mm"
include "cmul.mm"
include "co.mm"
include "wne.mm"
include "wrex.mm"
include "wcel.mm"
include "c2.mm"
include "2even.mm"
include "a1i.mm"
include "wceq.mm"
include "wb.mm"
include "oveq2.mm"
include "id.mm"
include "neeq12d.mm"
include "adantl.mm"
include "cc.mm"
include "cz.mm"
include "crab.mm"
include "elrabi.mm"
include "zcnd.mm"
include "eleq2s.mm"
include "wa.mm"
include "cdiv.mm"
include "c1.mm"
include "wnel.mm"
include "1neven.mm"
include "elnelne2.mm"
include "mpan2.mm"
include "adantr.mm"
include "simpr.mm"
include "2cnd.mm"
include "cc0.mm"
include "2ne0.mm"
include "divcan4d.mm"
include "2cnne0.mm"
include "divid.mm"
include "mp1i.mm"
include "3netr4d.mm"
include "mulcld.mm"
include "div11.mm"
include "syl3anc.mm"
include "biimprd.mm"
include "necon3d.mm"
include "mpd.mm"
include "mpdan.mm"
include "rspcedvd.mm"
include "rgen.mm"

theorem 2zrngnmlid
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
  disjoint E a
  disjoint E b
  disjoint a b
  disjoint R a
  disjoint R b
  disjoint a x
  disjoint a z
  disjoint b x
  disjoint b z
  disjoint R x
  disjoint R z
  disjoint E x
  disjoint E z
  disjoint M a
  disjoint M b
  disjoint a y
  disjoint b y
  disjoint x y
  disjoint y z
  disjoint R y
  disjoint E y
  disjoint M y
  disjoint k x
  assert |- A. b e. E E. a e. E ( b x. a ) =/= a

  proof
    vb
    cv
    #
    va
    cv
    #
    cmul
    co
    #
    @1
    wne
    #
    va
    cE
    wrex
    vb
    cE
    @0
    cE
    wcel
    #
    @3
    @0
    c2
    cmul
    co
    #
    c2
    wne
    #
    va
    c2
    cE
    c2
    cE
    wcel
    @4
    vx
    vz
    cE
    2zrng.e
    2even
    a1i
    @1
    c2
    wceq
    #
    @3
    @6
    wb
    @4
    @7
    @2
    @5
    @1
    c2
    @1
    c2
    @0
    cmul
    oveq2
    @7
    id
    neeq12d
    adantl
    @4
    @0
    cc
    wcel
    #
    @6
    @8
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
    @10
    wcel
    @0
    @9
    vz
    @0
    cz
    elrabi
    zcnd
    2zrng.e
    eleq2s
    @4
    @8
    wa
    #
    @5
    c2
    cdiv
    co
    #
    c2
    c2
    cdiv
    co
    #
    wne
    @6
    @11
    @0
    c1
    @12
    @13
    @4
    @0
    c1
    wne
    #
    @8
    @4
    c1
    cE
    wnel
    @14
    vx
    vz
    cE
    2zrng.e
    1neven
    @0
    c1
    cE
    elnelne2
    mpan2
    adantr
    @11
    @0
    c2
    @4
    @8
    simpr
    #
    @11
    2cnd
    #
    c2
    cc0
    wne
    #
    @11
    2ne0
    a1i
    divcan4d
    c2
    cc
    wcel
    #
    @17
    wa
    #
    @13
    c1
    wceq
    @11
    2cnne0
    c2
    divid
    mp1i
    3netr4d
    @11
    @5
    c2
    @12
    @13
    @11
    @12
    @13
    wceq
    #
    @5
    c2
    wceq
    #
    @11
    @5
    cc
    wcel
    @18
    @19
    @20
    @21
    wb
    @11
    @0
    c2
    @15
    @16
    mulcld
    @16
    @19
    @11
    2cnne0
    a1i
    @5
    c2
    c2
    div11
    syl3anc
    biimprd
    necon3d
    mpd
    mpdan
    rspcedvd
    rgen
end
