include "cv.mm"
include "cfv.mm"
include "c-bnj14.mm"
include "cres.mm"
include "cop.mm"
include "wceq.mm"
include "cuni.mm"
include "wfn.mm"
include "wral.mm"
include "wa.mm"
include "wrex.mm"
include "bnj1317.mm"
include "nfcii.mm"
include "nfuni.mm"
include "nfcxfr.mm"
include "nfcv.mm"
include "nffv.mm"
include "nfres.mm"
include "nfop.mm"
include "nfeq.mm"
include "nf5ri.mm"

theorem bnj1520
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let vf: setvar f
  let cF: class F
  let cG: class G
  let cY: class Y
  let vd: setvar d
  let vw: setvar w
  assume bnj1520.1: |- B = { d | ( d C_ A /\ A. x e. d _pred ( x , A , R ) C_ d ) }
  assume bnj1520.2: |- Y = <. x , ( f |` _pred ( x , A , R ) ) >.
  assume bnj1520.3: |- C = { f | E. d e. B ( f Fn d /\ A. x e. d ( f ` x ) = ( G ` Y ) ) }
  assume bnj1520.4: |- F = U. C

  disjoint A f
  disjoint G f
  disjoint R f
  disjoint f x
  disjoint A w
  disjoint f w
  disjoint C w
  disjoint F w
  disjoint G w
  disjoint R w
  disjoint w x
  assert |- ( ( F ` x ) = ( G ` <. x , ( F |` _pred ( x , A , R ) ) >. ) -> A. f ( F ` x ) = ( G ` <. x , ( F |` _pred ( x , A , R ) ) >. ) )

  proof
    vx
    cv
    #
    cF
    cfv
    #
    @0
    cF
    cA
    cR
    @0
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
    vf
    vf
    @1
    @5
    vf
    @0
    cF
    vf
    cF
    cC
    cuni
    bnj1520.4
    vf
    cC
    vf
    vw
    cC
    vf
    cv
    #
    vd
    cv
    #
    wfn
    @0
    @6
    cfv
    cY
    cG
    cfv
    wceq
    vx
    @7
    wral
    wa
    vd
    cB
    wrex
    vf
    vw
    cC
    bnj1520.3
    bnj1317
    nfcii
    nfuni
    nfcxfr
    #
    vf
    @0
    nfcv
    #
    nffv
    vf
    @4
    cG
    vf
    cG
    nfcv
    vf
    @0
    @3
    @9
    vf
    cF
    @2
    @8
    vf
    @2
    nfcv
    nfres
    nfop
    nffv
    nfeq
    nf5ri
end
