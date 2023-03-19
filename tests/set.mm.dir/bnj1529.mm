include "cv.mm"
include "cfv.mm"
include "c-bnj14.mm"
include "cres.mm"
include "cop.mm"
include "wceq.mm"
include "wral.mm"
include "nfv.mm"
include "nfcii.mm"
include "nfcv.mm"
include "nffv.mm"
include "nfres.mm"
include "nfop.mm"
include "nfeq.mm"
include "fveq2.mm"
include "id.mm"
include "bnj602.mm"
include "reseq2d.mm"
include "opeq12d.mm"
include "fveq2d.mm"
include "eqeq12d.mm"
include "cbvral.mm"
include "sylib.mm"

theorem bnj1529
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y
  let vw: setvar w
  let cA: class A
  let cR: class R
  let cF: class F
  let cG: class G
  assume bnj1529.1: |- ( ch -> A. x e. A ( F ` x ) = ( G ` <. x , ( F |` _pred ( x , A , R ) ) >. ) )
  assume bnj1529.2: |- ( w e. F -> A. x w e. F )

  disjoint A w
  disjoint A x
  disjoint A y
  disjoint w x
  disjoint w y
  disjoint x y
  disjoint F w
  disjoint F y
  disjoint G w
  disjoint G x
  disjoint G y
  disjoint R w
  disjoint R x
  disjoint R y
  assert |- ( ch -> A. y e. A ( F ` y ) = ( G ` <. y , ( F |` _pred ( y , A , R ) ) >. ) )

  proof
    wch
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
    #
    vx
    cA
    wral
    vy
    cv
    #
    cF
    cfv
    #
    @7
    cF
    cA
    cR
    @7
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
    vy
    cA
    wral
    bnj1529.1
    @6
    @13
    vx
    vy
    cA
    @6
    vy
    nfv
    vx
    @8
    @12
    vx
    @7
    cF
    vx
    vw
    cF
    bnj1529.2
    nfcii
    #
    vx
    @7
    nfcv
    #
    nffv
    vx
    @11
    cG
    vx
    cG
    nfcv
    vx
    @7
    @10
    @15
    vx
    cF
    @9
    @14
    vx
    @9
    nfcv
    nfres
    nfop
    nffv
    nfeq
    @0
    @7
    wceq
    #
    @1
    @8
    @5
    @12
    @0
    @7
    cF
    fveq2
    @16
    @4
    @11
    cG
    @16
    @0
    @7
    @3
    @10
    @16
    id
    @16
    @2
    @9
    cF
    cA
    cR
    @0
    @7
    bnj602
    reseq2d
    opeq12d
    fveq2d
    eqeq12d
    cbvral
    sylib
end
