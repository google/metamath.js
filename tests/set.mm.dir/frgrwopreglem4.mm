include "cfrgr.mm"
include "wcel.mm"
include "cv.mm"
include "cpr.mm"
include "wa.mm"
include "cfv.mm"
include "wne.mm"
include "simpl.mm"
include "wceq.mm"
include "crab.mm"
include "elrabi.mm"
include "eleq2s.mm"
include "cdif.mm"
include "eldifi.mm"
include "anim12i.mm"
include "adantl.mm"
include "frgrwopreglem3.mm"
include "frgrwopreglem4a.mm"
include "syl3anc.mm"
include "ralrimivva.mm"

theorem frgrwopreglem4
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cD: class D
  let cE: class E
  let cG: class G
  let cK: class K
  let cV: class V
  let va: setvar a
  let vb: setvar b
  let vy: setvar y
  let cX: class X
  let cY: class Y
  assume frgrwopreg.v: |- V = ( Vtx ` G )
  assume frgrwopreg.d: |- D = ( VtxDeg ` G )
  assume frgrwopreg.a: |- A = { x e. V | ( D ` x ) = K }
  assume frgrwopreg.b: |- B = ( V \ A )
  assume frgrwopreg.e: |- E = ( Edg ` G )

  disjoint A b
  disjoint B x
  disjoint G a
  disjoint G b
  disjoint G x
  disjoint a b
  disjoint a x
  disjoint b x
  disjoint V x
  disjoint A x
  disjoint G x
  disjoint K x
  disjoint D x
  disjoint D y
  disjoint G y
  disjoint a y
  disjoint b y
  disjoint x y
  disjoint V y
  disjoint X x
  disjoint Y x
  assert |- ( G e. FriendGraph -> A. a e. A A. b e. B { a , b } e. E )

  proof
    cG
    cfrgr
    wcel
    #
    va
    cv
    #
    vb
    cv
    #
    cpr
    cE
    wcel
    #
    va
    vb
    cA
    cB
    @0
    @1
    cA
    wcel
    #
    @2
    cB
    wcel
    #
    wa
    #
    wa
    @0
    @1
    cV
    wcel
    #
    @2
    cV
    wcel
    #
    wa
    #
    @1
    cD
    cfv
    @2
    cD
    cfv
    wne
    #
    @3
    @0
    @6
    simpl
    @6
    @9
    @0
    @4
    @7
    @5
    @8
    @7
    @1
    vx
    cv
    cD
    cfv
    cK
    wceq
    #
    vx
    cV
    crab
    cA
    @11
    vx
    @1
    cV
    elrabi
    frgrwopreg.a
    eleq2s
    @8
    @2
    cV
    cA
    cdif
    cB
    @2
    cV
    cA
    eldifi
    frgrwopreg.b
    eleq2s
    anim12i
    adantl
    @6
    @10
    @0
    vx
    cA
    cB
    cD
    cG
    cK
    cV
    @1
    @2
    frgrwopreg.v
    frgrwopreg.d
    frgrwopreg.a
    frgrwopreg.b
    frgrwopreglem3
    adantl
    cD
    cE
    cG
    cV
    @1
    @2
    frgrwopreg.v
    frgrwopreg.d
    frgrwopreg.e
    frgrwopreglem4a
    syl3anc
    ralrimivva
end
