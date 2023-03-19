include "cvv.mm"
include "wcel.mm"
include "wn.mm"
include "csuc.mm"
include "cfv.mm"
include "cmpt.mm"
include "crdg.mm"
include "c0.mm"
include "fveq1i.mm"
include "cdm.mm"
include "wceq.mm"
include "wlim.mm"
include "wb.mm"
include "rdgdmlim.mm"
include "limsuc.mm"
include "ax-mp.mm"
include "rdgsucg.mm"
include "fveq2i.mm"
include "syl6eqr.mm"
include "nfmpt1.mm"
include "nfrdg.mm"
include "nfcxfr.mm"
include "nffv.mm"
include "eqid.mm"
include "fvmptnf.mm"
include "sylan9eqr.mm"
include "ex.mm"
include "syl5bir.mm"
include "ndmfv.mm"
include "pm2.61d1.mm"
include "syl5eq.mm"

theorem rdgsucmptnf
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cF: class F
  assume rdgsucmptf.1: |- F/_ x A
  assume rdgsucmptf.2: |- F/_ x B
  assume rdgsucmptf.3: |- F/_ x D
  assume rdgsucmptf.4: |- F = rec ( ( x e. _V |-> C ) , A )
  assume rdgsucmptf.5: |- ( x = ( F ` B ) -> C = D )


  assert |- ( -. D e. _V -> ( F ` suc B ) = (/) )

  proof
    cD
    cvv
    wcel
    wn
    #
    cB
    csuc
    #
    cF
    cfv
    @1
    vx
    cvv
    cC
    cmpt
    #
    cA
    crdg
    #
    cfv
    #
    c0
    @1
    cF
    @3
    rdgsucmptf.4
    fveq1i
    @0
    @1
    @3
    cdm
    #
    wcel
    #
    @4
    c0
    wceq
    #
    @6
    cB
    @5
    wcel
    #
    @0
    @7
    @5
    wlim
    @8
    @6
    wb
    cA
    @2
    rdgdmlim
    @5
    cB
    limsuc
    ax-mp
    @0
    @8
    @7
    @8
    @0
    @4
    cB
    cF
    cfv
    #
    @2
    cfv
    #
    c0
    @8
    @4
    cB
    @3
    cfv
    #
    @2
    cfv
    @10
    cA
    cB
    @2
    rdgsucg
    @9
    @11
    @2
    cB
    cF
    @3
    rdgsucmptf.4
    fveq1i
    fveq2i
    syl6eqr
    vx
    @9
    cC
    cD
    cvv
    @2
    vx
    cB
    cF
    vx
    cF
    @3
    rdgsucmptf.4
    vx
    cA
    @2
    vx
    cvv
    cC
    nfmpt1
    rdgsucmptf.1
    nfrdg
    nfcxfr
    rdgsucmptf.2
    nffv
    rdgsucmptf.3
    rdgsucmptf.5
    @2
    eqid
    fvmptnf
    sylan9eqr
    ex
    syl5bir
    @1
    @3
    ndmfv
    pm2.61d1
    syl5eq
end
