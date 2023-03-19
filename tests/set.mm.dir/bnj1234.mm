include "cv.mm"
include "wfn.mm"
include "cfv.mm"
include "wceq.mm"
include "wral.mm"
include "wa.mm"
include "wrex.mm"
include "cab.mm"
include "fneq1.mm"
include "fveq1.mm"
include "c-bnj14.mm"
include "cres.mm"
include "cop.mm"
include "reseq1.mm"
include "opeq2d.mm"
include "3eqtr4g.mm"
include "fveq2d.mm"
include "eqeq12d.mm"
include "ralbidv.mm"
include "anbi12d.mm"
include "rexbidv.mm"
include "cbvabv.mm"
include "3eqtr4i.mm"

theorem bnj1234
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  let vf: setvar f
  let vg: setvar g
  let cG: class G
  let cY: class Y
  let cZ: class Z
  let vd: setvar d
  assume bnj1234.2: |- Y = <. x , ( f |` _pred ( x , A , R ) ) >.
  assume bnj1234.3: |- C = { f | E. d e. B ( f Fn d /\ A. x e. d ( f ` x ) = ( G ` Y ) ) }
  assume bnj1234.4: |- Z = <. x , ( g |` _pred ( x , A , R ) ) >.
  assume bnj1234.5: |- D = { g | E. d e. B ( g Fn d /\ A. x e. d ( g ` x ) = ( G ` Z ) ) }

  disjoint B f
  disjoint B g
  disjoint f g
  disjoint G f
  disjoint G g
  disjoint Y g
  disjoint Z f
  disjoint d f
  disjoint d g
  disjoint f x
  disjoint g x
  assert |- C = D

  proof
    vf
    cv
    #
    vd
    cv
    #
    wfn
    #
    vx
    cv
    #
    @0
    cfv
    #
    cY
    cG
    cfv
    #
    wceq
    #
    vx
    @1
    wral
    #
    wa
    #
    vd
    cB
    wrex
    #
    vf
    cab
    vg
    cv
    #
    @1
    wfn
    #
    @3
    @10
    cfv
    #
    cZ
    cG
    cfv
    #
    wceq
    #
    vx
    @1
    wral
    #
    wa
    #
    vd
    cB
    wrex
    #
    vg
    cab
    cC
    cD
    @9
    @17
    vf
    vg
    @0
    @10
    wceq
    #
    @8
    @16
    vd
    cB
    @18
    @2
    @11
    @7
    @15
    @1
    @0
    @10
    fneq1
    @18
    @6
    @14
    vx
    @1
    @18
    @4
    @12
    @5
    @13
    @3
    @0
    @10
    fveq1
    @18
    cY
    cZ
    cG
    @18
    @3
    @0
    cA
    cR
    @3
    c-bnj14
    #
    cres
    #
    cop
    @3
    @10
    @19
    cres
    #
    cop
    cY
    cZ
    @18
    @20
    @21
    @3
    @0
    @10
    @19
    reseq1
    opeq2d
    bnj1234.2
    bnj1234.4
    3eqtr4g
    fveq2d
    eqeq12d
    ralbidv
    anbi12d
    rexbidv
    cbvabv
    bnj1234.3
    bnj1234.5
    3eqtr4i
end
