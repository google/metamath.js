include "wcel.mm"
include "cbs.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "crg.mm"
include "abvrcl.mm"
include "eqid.mm"
include "ring0cl.mm"
include "syl.mm"
include "wa.mm"
include "abveq0.mm"
include "mpbiri.mm"
include "mpdan.mm"

theorem abv0
  let cA: class A
  let cR: class R
  let cF: class F
  let c.0: class .0.
  assume abv0.a: |- A = ( AbsVal ` R )
  assume abv0.z: |- .0. = ( 0g ` R )


  assert |- ( F e. A -> ( F ` .0. ) = 0 )

  proof
    cF
    cA
    wcel
    #
    c.0
    cR
    cbs
    cfv
    #
    wcel
    #
    c.0
    cF
    cfv
    cc0
    wceq
    #
    @0
    cR
    crg
    wcel
    @2
    cA
    cR
    cF
    abv0.a
    abvrcl
    @1
    cR
    c.0
    @1
    eqid
    #
    abv0.z
    ring0cl
    syl
    @0
    @2
    wa
    @3
    c.0
    c.0
    wceq
    c.0
    eqid
    cA
    @1
    cR
    cF
    c.0
    c.0
    abv0.a
    @4
    abv0.z
    abveq0
    mpbiri
    mpdan
end
