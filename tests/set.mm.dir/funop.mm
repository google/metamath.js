include "cop.mm"
include "wfun.mm"
include "cv.mm"
include "csn.mm"
include "wceq.mm"
include "wa.mm"
include "wex.mm"
include "eqid.mm"
include "funopsn.mm"
include "mpan2.mm"
include "vex.mm"
include "funsn.mm"
include "funeq.mm"
include "mpbiri.mm"
include "adantl.mm"
include "exlimiv.mm"
include "impbii.mm"

theorem funop
  let cX: class X
  let cY: class Y
  let va: setvar a
  let cF: class F
  let vx: setvar x
  assume funopsn.x: |- X e. _V
  assume funopsn.y: |- Y e. _V

  disjoint X a
  disjoint Y a
  disjoint F a
  disjoint F x
  disjoint a x
  disjoint X x
  disjoint Y x
  assert |- ( Fun <. X , Y >. <-> E. a ( X = { a } /\ <. X , Y >. = { <. a , a >. } ) )

  proof
    cX
    cY
    cop
    #
    wfun
    #
    cX
    va
    cv
    #
    csn
    wceq
    #
    @0
    @2
    @2
    cop
    csn
    #
    wceq
    #
    wa
    #
    va
    wex
    #
    @1
    @0
    @0
    wceq
    @7
    @0
    eqid
    @0
    cX
    cY
    va
    funopsn.x
    funopsn.y
    funopsn
    mpan2
    @6
    @1
    va
    @5
    @1
    @3
    @5
    @1
    @4
    wfun
    @2
    @2
    va
    vex
    #
    @8
    funsn
    @0
    @4
    funeq
    mpbiri
    adantl
    exlimiv
    impbii
end
