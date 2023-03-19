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
include "cab.mm"
include "nfre1.mm"
include "nfab.mm"
include "nfcxfr.mm"
include "nfuni.mm"
include "nfcv.mm"
include "nffv.mm"
include "nfres.mm"
include "nfop.mm"
include "nfeq.mm"
include "nf5ri.mm"

theorem bnj1519
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
  assume bnj1519.1: |- B = { d | ( d C_ A /\ A. x e. d _pred ( x , A , R ) C_ d ) }
  assume bnj1519.2: |- Y = <. x , ( f |` _pred ( x , A , R ) ) >.
  assume bnj1519.3: |- C = { f | E. d e. B ( f Fn d /\ A. x e. d ( f ` x ) = ( G ` Y ) ) }
  assume bnj1519.4: |- F = U. C

  disjoint A d
  disjoint G d
  disjoint R d
  disjoint d x
  assert |- ( ( F ` x ) = ( G ` <. x , ( F |` _pred ( x , A , R ) ) >. ) -> A. d ( F ` x ) = ( G ` <. x , ( F |` _pred ( x , A , R ) ) >. ) )

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
    vd
    vd
    @1
    @5
    vd
    @0
    cF
    vd
    cF
    cC
    cuni
    bnj1519.4
    vd
    cC
    vd
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
    #
    vd
    cB
    wrex
    #
    vf
    cab
    bnj1519.3
    @9
    vd
    vf
    @8
    vd
    cB
    nfre1
    nfab
    nfcxfr
    nfuni
    nfcxfr
    #
    vd
    @0
    nfcv
    #
    nffv
    vd
    @4
    cG
    vd
    cG
    nfcv
    vd
    @0
    @3
    @11
    vd
    cF
    @2
    @10
    vd
    @2
    nfcv
    nfres
    nfop
    nffv
    nfeq
    nf5ri
end
