include "cv.mm"
include "wcel.mm"
include "wbr.mm"
include "wn.mm"
include "wral.mm"
include "wa.mm"
include "c-bnj14.mm"
include "cin.mm"
include "c0.mm"
include "wne.mm"
include "wceq.mm"
include "w3a.mm"
include "wex.mm"
include "n0.mm"
include "elin.mm"
include "exbii.mm"
include "sylbb.mm"
include "df-bnj14.mm"
include "bnj1538.mm"
include "anim1i.mm"
include "bnj593.mm"
include "3ad2ant3.mm"
include "nfv.mm"
include "nfra1.mm"
include "nf3an.mm"
include "nf5ri.mm"
include "bnj1275.mm"
include "simp2.mm"
include "simp12.mm"
include "simp3.mm"
include "bnj1294.mm"
include "bnj1304.mm"
include "bnj1224.mm"
include "nne.mm"
include "sylib.mm"

theorem bnj1279
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let cE: class E
  let cG: class G
  let cY: class Y
  let vd: setvar d
  assume bnj1279.1: |- B = { d | ( d C_ A /\ A. x e. d _pred ( x , A , R ) C_ d ) }
  assume bnj1279.2: |- Y = <. x , ( f |` _pred ( x , A , R ) ) >.
  assume bnj1279.3: |- C = { f | E. d e. B ( f Fn d /\ A. x e. d ( f ` x ) = ( G ` Y ) ) }
  assume bnj1279.4: |- D = ( dom g i^i dom h )
  assume bnj1279.5: |- E = { x e. D | ( g ` x ) =/= ( h ` x ) }
  assume bnj1279.6: |- ( ph <-> ( R _FrSe A /\ g e. C /\ h e. C /\ ( g |` D ) =/= ( h |` D ) ) )
  assume bnj1279.7: |- ( ps <-> ( ph /\ x e. E /\ A. y e. E -. y R x ) )

  disjoint A y
  disjoint E y
  disjoint R y
  disjoint x y
  assert |- ( ( x e. E /\ A. y e. E -. y R x ) -> ( _pred ( x , A , R ) i^i E ) = (/) )

  proof
    vx
    cv
    #
    cE
    wcel
    #
    vy
    cv
    #
    @0
    cR
    wbr
    #
    wn
    #
    vy
    cE
    wral
    #
    wa
    cA
    cR
    @0
    c-bnj14
    #
    cE
    cin
    #
    c0
    wne
    #
    wn
    @7
    c0
    wceq
    @1
    @5
    @8
    @1
    @5
    @8
    w3a
    #
    @9
    @3
    @2
    cE
    wcel
    #
    w3a
    #
    @3
    vy
    @9
    @3
    @10
    vy
    @8
    @1
    @3
    @10
    wa
    #
    vy
    wex
    @5
    @8
    @2
    @6
    wcel
    #
    @10
    wa
    #
    @12
    vy
    @8
    @2
    @7
    wcel
    #
    vy
    wex
    @14
    vy
    wex
    vy
    @7
    n0
    @15
    @14
    vy
    @2
    @6
    cE
    elin
    exbii
    sylbb
    @13
    @3
    @10
    @3
    vy
    @6
    cA
    vy
    cA
    cR
    @0
    df-bnj14
    bnj1538
    anim1i
    bnj593
    3ad2ant3
    @9
    vy
    @1
    @5
    @8
    vy
    @1
    vy
    nfv
    @4
    vy
    cE
    nfra1
    @8
    vy
    nfv
    nf3an
    nf5ri
    bnj1275
    @9
    @3
    @10
    simp2
    @11
    @4
    vy
    cE
    @1
    @5
    @8
    @3
    @10
    simp12
    @9
    @3
    @10
    simp3
    bnj1294
    bnj1304
    bnj1224
    @7
    c0
    nne
    sylib
end
