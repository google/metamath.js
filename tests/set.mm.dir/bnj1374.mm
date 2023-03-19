include "cv.mm"
include "wcel.mm"
include "cdm.mm"
include "csn.mm"
include "c-bnj18.mm"
include "cun.mm"
include "wceq.mm"
include "wa.mm"
include "wex.mm"
include "c-bnj14.mm"
include "wrex.mm"
include "bnj1436.mm"
include "rexex.mm"
include "syl.mm"
include "bnj1373.mm"
include "exbii.mm"
include "sylib.mm"
include "exsimpl.mm"
include "bnj937.mm"

theorem bnj1374
  let wps: wff ps
  let wch: wff ch
  let wta: wff ta
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  let vf: setvar f
  let cG: class G
  let cH: class H
  let cY: class Y
  let vd: setvar d
  let bnjwtam: wff ta'
  assume bnj1374.1: |- B = { d | ( d C_ A /\ A. x e. d _pred ( x , A , R ) C_ d ) }
  assume bnj1374.2: |- Y = <. x , ( f |` _pred ( x , A , R ) ) >.
  assume bnj1374.3: |- C = { f | E. d e. B ( f Fn d /\ A. x e. d ( f ` x ) = ( G ` Y ) ) }
  assume bnj1374.4: |- ( ta <-> ( f e. C /\ dom f = ( { x } u. _trCl ( x , A , R ) ) ) )
  assume bnj1374.5: |- D = { x e. A | -. E. f ta }
  assume bnj1374.6: |- ( ps <-> ( R _FrSe A /\ D =/= (/) ) )
  assume bnj1374.7: |- ( ch <-> ( ps /\ x e. D /\ A. y e. D -. y R x ) )
  assume bnj1374.8: |- ( ta' <-> [. y / x ]. ta )
  assume bnj1374.9: |- H = { f | E. y e. _pred ( x , A , R ) ta' }

  disjoint A x
  disjoint B f
  disjoint C y
  disjoint R x
  disjoint d f
  disjoint d x
  disjoint f x
  disjoint f y
  disjoint x y
  assert |- ( f e. H -> f e. C )

  proof
    vf
    cv
    #
    cH
    wcel
    #
    @0
    cC
    wcel
    #
    vy
    @1
    @2
    @0
    cdm
    vy
    cv
    #
    csn
    cA
    cR
    @3
    c-bnj18
    cun
    wceq
    #
    wa
    #
    vy
    wex
    #
    @2
    vy
    wex
    @1
    bnjwtam
    vy
    wex
    #
    @6
    @1
    bnjwtam
    vy
    cA
    cR
    vx
    cv
    c-bnj14
    #
    wrex
    #
    @7
    @9
    vf
    cH
    bnj1374.9
    bnj1436
    bnjwtam
    vy
    @8
    rexex
    syl
    bnjwtam
    @5
    vy
    wta
    vx
    vy
    cA
    cB
    cC
    cR
    vf
    cG
    cY
    vd
    bnjwtam
    bnj1374.1
    bnj1374.2
    bnj1374.3
    bnj1374.4
    bnj1374.8
    bnj1373
    exbii
    sylib
    @2
    @4
    vy
    exsimpl
    syl
    bnj937
end
