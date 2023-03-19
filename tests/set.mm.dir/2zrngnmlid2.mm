include "cv.mm"
include "cmul.mm"
include "co.mm"
include "wne.mm"
include "wral.mm"
include "cc0.mm"
include "csn.mm"
include "cdif.mm"
include "2zrngnmrid.mm"
include "wcel.mm"
include "wa.mm"
include "wceq.mm"
include "cc.mm"
include "eldifi.mm"
include "c2.mm"
include "cz.mm"
include "wrex.mm"
include "crab.mm"
include "elrabi.mm"
include "zcnd.mm"
include "eleq2s.mm"
include "syl.mm"
include "mulcom.mm"
include "syl2an.mm"
include "eqcomd.mm"
include "eqeq1d.mm"
include "biimpd.mm"
include "necon3d.mm"
include "ralimdva.mm"
include "ralimia.mm"
include "ax-mp.mm"

theorem 2zrngnmlid2
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
  assert |- A. a e. ( E \ { 0 } ) A. b e. E ( b x. a ) =/= a

  proof
    va
    cv
    #
    vb
    cv
    #
    cmul
    co
    #
    @0
    wne
    #
    vb
    cE
    wral
    #
    va
    cE
    cc0
    csn
    #
    cdif
    #
    wral
    @1
    @0
    cmul
    co
    #
    @0
    wne
    #
    vb
    cE
    wral
    #
    va
    @6
    wral
    vx
    vz
    cR
    cE
    cM
    va
    vb
    2zrng.e
    2zrngbas.r
    2zrngmmgm.1
    2zrngnmrid
    @4
    @9
    va
    @6
    @0
    @6
    wcel
    #
    @3
    @8
    vb
    cE
    @10
    @1
    cE
    wcel
    #
    wa
    #
    @7
    @0
    @2
    @0
    @12
    @7
    @0
    wceq
    @2
    @0
    wceq
    @12
    @7
    @2
    @0
    @12
    @2
    @7
    @10
    @0
    cc
    wcel
    #
    @1
    cc
    wcel
    #
    @2
    @7
    wceq
    @11
    @10
    @0
    cE
    wcel
    @13
    @0
    cE
    @5
    eldifi
    @13
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
    @16
    wcel
    @0
    @15
    vz
    @0
    cz
    elrabi
    zcnd
    2zrng.e
    eleq2s
    syl
    @14
    @1
    @16
    cE
    @1
    @16
    wcel
    @1
    @15
    vz
    @1
    cz
    elrabi
    zcnd
    2zrng.e
    eleq2s
    @0
    @1
    mulcom
    syl2an
    eqcomd
    eqeq1d
    biimpd
    necon3d
    ralimdva
    ralimia
    ax-mp
end
