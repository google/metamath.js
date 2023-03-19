include "cv.mm"
include "wcel.mm"
include "wfun.mm"
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
include "exbii.mm"
include "sylib.mm"
include "exsimpl.mm"
include "wfn.mm"
include "cfv.mm"
include "wral.mm"
include "abeq2i.mm"
include "bnj1238.mm"
include "fnfun.mm"
include "bnj31.mm"
include "bnj1265.mm"
include "bnj593.mm"
include "bnj937.mm"

theorem bnj1371
  let wps: wff ps
  let wch: wff ch
  let wta: wff ta
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cR: class R
  let vf: setvar f
  let cG: class G
  let cH: class H
  let cY: class Y
  let vd: setvar d
  let bnjwtam: wff ta'
  assume bnj1371.1: |- B = { d | ( d C_ A /\ A. x e. d _pred ( x , A , R ) C_ d ) }
  assume bnj1371.2: |- Y = <. x , ( f |` _pred ( x , A , R ) ) >.
  assume bnj1371.3: |- C = { f | E. d e. B ( f Fn d /\ A. x e. d ( f ` x ) = ( G ` Y ) ) }
  assume bnj1371.4: |- ( ta <-> ( f e. C /\ dom f = ( { x } u. _trCl ( x , A , R ) ) ) )
  assume bnj1371.5: |- D = { x e. A | -. E. f ta }
  assume bnj1371.6: |- ( ps <-> ( R _FrSe A /\ D =/= (/) ) )
  assume bnj1371.7: |- ( ch <-> ( ps /\ x e. D /\ A. y e. D -. y R x ) )
  assume bnj1371.8: |- ( ta' <-> [. y / x ]. ta )
  assume bnj1371.9: |- H = { f | E. y e. _pred ( x , A , R ) ta' }
  assume bnj1371.10: |- P = U. H
  assume bnj1371.11: |- ( ta' <-> ( f e. C /\ dom f = ( { y } u. _trCl ( y , A , R ) ) ) )

  disjoint d f
  disjoint f y
  assert |- ( f e. H -> Fun f )

  proof
    vf
    cv
    #
    cH
    wcel
    #
    @0
    wfun
    #
    vy
    @1
    @0
    cC
    wcel
    #
    @2
    vy
    @1
    @3
    @0
    cdm
    vy
    cv
    #
    csn
    cA
    cR
    @4
    c-bnj18
    cun
    wceq
    #
    wa
    #
    vy
    wex
    #
    @3
    vy
    wex
    @1
    bnjwtam
    vy
    wex
    #
    @7
    @1
    bnjwtam
    vy
    cA
    cR
    vx
    cv
    #
    c-bnj14
    #
    wrex
    #
    @8
    @11
    vf
    cH
    bnj1371.9
    bnj1436
    bnjwtam
    vy
    @10
    rexex
    syl
    bnjwtam
    @6
    vy
    bnj1371.11
    exbii
    sylib
    @3
    @5
    vy
    exsimpl
    syl
    @3
    @2
    vd
    cB
    @3
    @0
    vd
    cv
    #
    wfn
    #
    @2
    vd
    cB
    @3
    @13
    @9
    @0
    cfv
    cY
    cG
    cfv
    wceq
    vx
    @12
    wral
    #
    vd
    cB
    @13
    @14
    wa
    vd
    cB
    wrex
    vf
    cC
    bnj1371.3
    abeq2i
    bnj1238
    @12
    @0
    fnfun
    bnj31
    bnj1265
    bnj593
    bnj937
end
