include "wcel.mm"
include "cfv.mm"
include "wceq.mm"
include "csb.mm"
include "cid.mm"
include "cv.mm"
include "csbeq1.mm"
include "cmpt.mm"
include "nfcv.mm"
include "nfcsb1v.mm"
include "csbeq1a.mm"
include "cbvmpt.mm"
include "eqtri.mm"
include "fvmpti.mm"
include "fveq2d.mm"
include "nffv.mm"
include "fvex.mm"
include "fvmpt.mm"
include "eqtr4d.mm"
include "wn.mm"
include "c0.mm"
include "cdm.mm"
include "dmmptss.mm"
include "sseli.mm"
include "con3i.mm"
include "ndmfv.mm"
include "syl.mm"
include "dmmpti.mm"
include "eleq2i.mm"
include "sylnbir.mm"
include "pm2.61i.mm"

theorem fvmptex
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let cG: class G
  let vy: setvar y
  assume fvmptex.1: |- F = ( x e. A |-> B )
  assume fvmptex.2: |- G = ( x e. A |-> ( _I ` B ) )

  disjoint A x
  disjoint x y
  disjoint A y
  disjoint B y
  disjoint C y
  assert |- ( F ` C ) = ( G ` C )

  proof
    cC
    cA
    wcel
    #
    cC
    cF
    cfv
    #
    cC
    cG
    cfv
    #
    wceq
    @0
    @1
    vx
    cC
    cB
    csb
    #
    cid
    cfv
    #
    @2
    vy
    cC
    vx
    vy
    cv
    #
    cB
    csb
    #
    @3
    cA
    cF
    vx
    @5
    cC
    cB
    csbeq1
    #
    cF
    vx
    cA
    cB
    cmpt
    vy
    cA
    @6
    cmpt
    fvmptex.1
    vx
    vy
    cA
    cB
    @6
    vy
    cB
    nfcv
    vx
    @5
    cB
    nfcsb1v
    #
    vx
    @5
    cB
    csbeq1a
    #
    cbvmpt
    eqtri
    fvmpti
    vy
    cC
    @6
    cid
    cfv
    #
    @4
    cA
    cG
    @5
    cC
    wceq
    @6
    @3
    cid
    @7
    fveq2d
    cG
    vx
    cA
    cB
    cid
    cfv
    #
    cmpt
    vy
    cA
    @10
    cmpt
    fvmptex.2
    vx
    vy
    cA
    @11
    @10
    vy
    @11
    nfcv
    vx
    @6
    cid
    vx
    cid
    nfcv
    @8
    nffv
    vx
    cv
    @5
    wceq
    cB
    @6
    cid
    @9
    fveq2d
    cbvmpt
    eqtri
    @3
    cid
    fvex
    fvmpt
    eqtr4d
    @0
    wn
    #
    @1
    c0
    @2
    @12
    cC
    cF
    cdm
    #
    wcel
    #
    wn
    @1
    c0
    wceq
    @14
    @0
    @13
    cA
    cC
    vx
    cA
    cB
    cF
    fvmptex.1
    dmmptss
    sseli
    con3i
    cC
    cF
    ndmfv
    syl
    @0
    cC
    cG
    cdm
    #
    wcel
    @2
    c0
    wceq
    @15
    cA
    cC
    vx
    cA
    @11
    cG
    cB
    cid
    fvex
    fvmptex.2
    dmmpti
    eleq2i
    cC
    cG
    ndmfv
    sylnbir
    eqtr4d
    pm2.61i
end
