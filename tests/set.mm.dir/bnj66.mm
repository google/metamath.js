include "cv.mm"
include "wcel.mm"
include "wfn.mm"
include "cfv.mm"
include "c-bnj14.mm"
include "cres.mm"
include "cop.mm"
include "wceq.mm"
include "wral.mm"
include "wa.mm"
include "wrex.mm"
include "wrel.mm"
include "cab.mm"
include "fneq1.mm"
include "fveq1.mm"
include "reseq1.mm"
include "opeq2d.mm"
include "syl6eqr.mm"
include "fveq2d.mm"
include "eqeq12d.mm"
include "ralbidv.mm"
include "anbi12d.mm"
include "rexbidv.mm"
include "cbvabv.mm"
include "eqtr4i.mm"
include "bnj1436.mm"
include "bnj1239.mm"
include "fnrel.mm"
include "rexlimivw.mm"
include "3syl.mm"

theorem bnj66
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let vf: setvar f
  let vg: setvar g
  let cG: class G
  let cY: class Y
  let vd: setvar d
  assume bnj66.1: |- B = { d | ( d C_ A /\ A. x e. d _pred ( x , A , R ) C_ d ) }
  assume bnj66.2: |- Y = <. x , ( f |` _pred ( x , A , R ) ) >.
  assume bnj66.3: |- C = { f | E. d e. B ( f Fn d /\ A. x e. d ( f ` x ) = ( G ` Y ) ) }

  disjoint A f
  disjoint B f
  disjoint B g
  disjoint f g
  disjoint G f
  disjoint G g
  disjoint R f
  disjoint Y g
  disjoint d f
  disjoint d g
  disjoint f x
  disjoint g x
  assert |- ( g e. C -> Rel g )

  proof
    vg
    cv
    #
    cC
    wcel
    @0
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
    #
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
    @2
    vd
    cB
    wrex
    @0
    wrel
    #
    @12
    vg
    cC
    cC
    vf
    cv
    #
    @1
    wfn
    #
    @3
    @14
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
    @12
    vg
    cab
    bnj66.3
    @12
    @21
    vg
    vf
    @0
    @14
    wceq
    #
    @11
    @20
    vd
    cB
    @22
    @2
    @15
    @10
    @19
    @1
    @0
    @14
    fneq1
    @22
    @9
    @18
    vx
    @1
    @22
    @4
    @16
    @8
    @17
    @3
    @0
    @14
    fveq1
    @22
    @7
    cY
    cG
    @22
    @7
    @3
    @14
    @5
    cres
    #
    cop
    cY
    @22
    @6
    @23
    @3
    @0
    @14
    @5
    reseq1
    opeq2d
    bnj66.2
    syl6eqr
    fveq2d
    eqeq12d
    ralbidv
    anbi12d
    rexbidv
    cbvabv
    eqtr4i
    bnj1436
    @2
    @10
    vd
    cB
    bnj1239
    @2
    @13
    vd
    cB
    @1
    @0
    fnrel
    rexlimivw
    3syl
end
