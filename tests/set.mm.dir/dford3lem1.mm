include "wtr.mm"
include "cv.mm"
include "wral.mm"
include "wa.mm"
include "treq.mm"
include "cbvralv.mm"
include "biimpi.mm"
include "adantl.mm"
include "wcel.mm"
include "wi.mm"
include "wss.mm"
include "trss.mm"
include "ssralv.mm"
include "syl6.mm"
include "com23.mm"
include "imp.mm"
include "ralrimiv.mm"
include "r19.26.mm"
include "sylanbrc.mm"

theorem dford3lem1
  let vy: setvar y
  let cN: class N
  let vb: setvar b
  let va: setvar a
  let vc: setvar c
  let vx: setvar x

  disjoint b y
  disjoint N b
  disjoint N y
  disjoint a b
  disjoint a c
  disjoint a x
  disjoint a y
  disjoint b c
  disjoint b x
  disjoint c x
  disjoint c y
  disjoint x y
  disjoint N a
  disjoint N c
  disjoint N x
  assert |- ( ( Tr N /\ A. y e. N Tr y ) -> A. b e. N ( Tr b /\ A. y e. b Tr y ) )

  proof
    cN
    wtr
    #
    vy
    cv
    #
    wtr
    #
    vy
    cN
    wral
    #
    wa
    #
    vb
    cv
    #
    wtr
    #
    vb
    cN
    wral
    #
    @2
    vy
    @5
    wral
    #
    vb
    cN
    wral
    @6
    @8
    wa
    vb
    cN
    wral
    @3
    @7
    @0
    @3
    @7
    @2
    @6
    vy
    vb
    cN
    @1
    @5
    treq
    cbvralv
    biimpi
    adantl
    @4
    @8
    vb
    cN
    @0
    @3
    @5
    cN
    wcel
    #
    @8
    wi
    @0
    @9
    @3
    @8
    @0
    @9
    @5
    cN
    wss
    @3
    @8
    wi
    cN
    @5
    trss
    @2
    vy
    @5
    cN
    ssralv
    syl6
    com23
    imp
    ralrimiv
    @6
    @8
    vb
    cN
    r19.26
    sylanbrc
end
