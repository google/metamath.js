include "cc0.mm"
include "wcel.mm"
include "ccmn.mm"
include "0even.mm"
include "caddc.mm"
include "cbs.mm"
include "cfv.mm"
include "wceq.mm"
include "2zrngbas.mm"
include "a1i.mm"
include "cplusg.mm"
include "2zrngadd.mm"
include "cmnd.mm"
include "2zrngamnd.mm"
include "cv.mm"
include "co.mm"
include "wa.mm"
include "cc.mm"
include "c2.mm"
include "cmul.mm"
include "cz.mm"
include "wrex.mm"
include "crab.mm"
include "elrabi.mm"
include "zcnd.mm"
include "eleq2s.mm"
include "adantr.mm"
include "adantl.mm"
include "addcomd.mm"
include "3adant1.mm"
include "iscmnd.mm"
include "ax-mp.mm"

theorem 2zrngacmnd
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
  assert |- R e. CMnd

  proof
    cc0
    cE
    wcel
    #
    cR
    ccmn
    wcel
    vx
    vz
    cE
    2zrng.e
    0even
    @0
    vx
    vy
    cE
    caddc
    cR
    cE
    cR
    cbs
    cfv
    wceq
    @0
    vx
    vz
    cR
    cE
    2zrng.e
    2zrngbas.r
    2zrngbas
    a1i
    caddc
    cR
    cplusg
    cfv
    wceq
    @0
    vx
    vz
    cR
    cE
    2zrng.e
    2zrngbas.r
    2zrngadd
    a1i
    cR
    cmnd
    wcel
    @0
    vx
    vz
    cR
    cE
    2zrng.e
    2zrngbas.r
    2zrngamnd
    a1i
    vx
    cv
    #
    cE
    wcel
    #
    vy
    cv
    #
    cE
    wcel
    #
    @1
    @3
    caddc
    co
    @3
    @1
    caddc
    co
    wceq
    @0
    @2
    @4
    wa
    @1
    @3
    @2
    @1
    cc
    wcel
    #
    @4
    @5
    @1
    vz
    cv
    c2
    @1
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
    @1
    @7
    wcel
    @1
    @6
    vz
    @1
    cz
    elrabi
    zcnd
    2zrng.e
    eleq2s
    adantr
    @4
    @3
    cc
    wcel
    #
    @2
    @8
    @3
    @7
    cE
    @3
    @7
    wcel
    @3
    @6
    vz
    @3
    cz
    elrabi
    zcnd
    2zrng.e
    eleq2s
    adantl
    addcomd
    3adant1
    iscmnd
    ax-mp
end
