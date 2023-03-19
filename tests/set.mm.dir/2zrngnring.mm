include "crg.mm"
include "wcel.mm"
include "cgrp.mm"
include "cmnd.mm"
include "cv.mm"
include "cplusg.mm"
include "cfv.mm"
include "co.mm"
include "cmul.mm"
include "wceq.mm"
include "wa.mm"
include "cbs.mm"
include "wral.mm"
include "w3a.mm"
include "wn.mm"
include "w3o.mm"
include "wne.mm"
include "wrex.mm"
include "2zrngnmlid.mm"
include "wnel.mm"
include "2zrngbas.mm"
include "mgpbas.mm"
include "2zrngmul.mm"
include "mgpplusg.mm"
include "isnmnd.mm"
include "df-nel.mm"
include "sylib.mm"
include "ax-mp.mm"
include "3mix2i.mm"
include "3ianor.mm"
include "mpbir.mm"
include "eqid.mm"
include "isring.mm"
include "mtbir.mm"
include "nelir.mm"

theorem 2zrngnring
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
  assert |- R e/ Ring

  proof
    cR
    crg
    cR
    crg
    wcel
    cR
    cgrp
    wcel
    #
    cM
    cmnd
    wcel
    #
    vx
    cv
    #
    vy
    cv
    #
    vz
    cv
    #
    cR
    cplusg
    cfv
    #
    co
    cmul
    co
    @2
    @3
    cmul
    co
    @2
    @4
    cmul
    co
    #
    @5
    co
    wceq
    @2
    @3
    @5
    co
    @4
    cmul
    co
    @6
    @3
    @4
    cmul
    co
    @5
    co
    wceq
    wa
    vz
    cR
    cbs
    cfv
    #
    wral
    vy
    @7
    wral
    vx
    @7
    wral
    #
    w3a
    #
    @9
    wn
    @0
    wn
    #
    @1
    wn
    #
    @8
    wn
    #
    w3o
    @11
    @10
    @12
    vb
    cv
    va
    cv
    #
    cmul
    co
    @13
    wne
    va
    cE
    wrex
    vb
    cE
    wral
    #
    @11
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
    2zrngnmlid
    @14
    cM
    cmnd
    wnel
    @11
    va
    vb
    cE
    cM
    cmul
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
    #
    mgpplusg
    isnmnd
    cM
    cmnd
    df-nel
    sylib
    ax-mp
    3mix2i
    @0
    @1
    @8
    3ianor
    mpbir
    vx
    vy
    vz
    @7
    @5
    cR
    cmul
    cM
    @7
    eqid
    2zrngmmgm.1
    @5
    eqid
    @15
    isring
    mtbir
    nelir
end
