include "cv.mm"
include "wcel.mm"
include "cfv.mm"
include "wceq.mm"
include "cdm.mm"
include "wral.mm"
include "wfn.mm"
include "w3a.mm"
include "wa.mm"
include "wrex.mm"
include "wex.mm"
include "bnj1436.mm"
include "df-rex.mm"
include "3anass.mm"
include "bnj133.mm"
include "sylib.mm"
include "simp3.mm"
include "fndm.mm"
include "3ad2ant2.mm"
include "raleqdv.mm"
include "mpbird.mm"
include "bnj593.mm"
include "bnj937.mm"

theorem bnj1514
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let vf: setvar f
  let cG: class G
  let cY: class Y
  let vd: setvar d
  assume bnj1514.1: |- B = { d | ( d C_ A /\ A. x e. d _pred ( x , A , R ) C_ d ) }
  assume bnj1514.2: |- Y = <. x , ( f |` _pred ( x , A , R ) ) >.
  assume bnj1514.3: |- C = { f | E. d e. B ( f Fn d /\ A. x e. d ( f ` x ) = ( G ` Y ) ) }

  disjoint A x
  disjoint G d
  disjoint Y d
  disjoint d f
  disjoint d x
  disjoint f x
  assert |- ( f e. C -> A. x e. dom f ( f ` x ) = ( G ` Y ) )

  proof
    vf
    cv
    #
    cC
    wcel
    #
    vx
    cv
    @0
    cfv
    cY
    cG
    cfv
    wceq
    #
    vx
    @0
    cdm
    #
    wral
    #
    vd
    @1
    vd
    cv
    #
    cB
    wcel
    #
    @0
    @5
    wfn
    #
    @2
    vx
    @5
    wral
    #
    w3a
    #
    @4
    vd
    @1
    @7
    @8
    wa
    #
    vd
    cB
    wrex
    #
    @9
    vd
    wex
    @11
    vf
    cC
    bnj1514.3
    bnj1436
    @11
    @6
    @10
    wa
    @9
    vd
    @10
    vd
    cB
    df-rex
    @6
    @7
    @8
    3anass
    bnj133
    sylib
    @9
    @4
    @8
    @6
    @7
    @8
    simp3
    @9
    @2
    vx
    @3
    @5
    @7
    @6
    @3
    @5
    wceq
    @8
    @5
    @0
    fndm
    3ad2ant2
    raleqdv
    mpbird
    bnj593
    bnj937
end
