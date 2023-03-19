include "wcel.mm"
include "ctop.mm"
include "wral.mm"
include "wa.mm"
include "cuni.mm"
include "cixp.mm"
include "cv.mm"
include "cmpt.mm"
include "cfv.mm"
include "wceq.mm"
include "eqid.mm"
include "fvmpt2.mm"
include "eqcomd.mm"
include "unieqd.mm"
include "ralimiaa.mm"
include "adantl.mm"
include "ixpeq2.mm"
include "syl.mm"
include "nffvmpt1.mm"
include "nfuni.mm"
include "nfcv.mm"
include "fveq2.mm"
include "cbvixp.mm"
include "syl6eqr.mm"
include "wf.mm"
include "fmpt.mm"
include "ptuni.mm"
include "sylan2b.mm"
include "eqtrd.mm"

theorem ptunimpt
  let vx: setvar x
  let cA: class A
  let cJ: class J
  let cK: class K
  let cV: class V
  let vy: setvar y
  assume ptunimpt.j: |- J = ( Xt_ ` ( x e. A |-> K ) )

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint K y
  disjoint V y
  assert |- ( ( A e. V /\ A. x e. A K e. Top ) -> X_ x e. A U. K = U. J )

  proof
    cA
    cV
    wcel
    #
    cK
    ctop
    wcel
    #
    vx
    cA
    wral
    #
    wa
    #
    vx
    cA
    cK
    cuni
    #
    cixp
    #
    vy
    cA
    vy
    cv
    #
    vx
    cA
    cK
    cmpt
    #
    cfv
    #
    cuni
    #
    cixp
    #
    cJ
    cuni
    #
    @3
    @5
    vx
    cA
    vx
    cv
    #
    @7
    cfv
    #
    cuni
    #
    cixp
    #
    @10
    @3
    @4
    @14
    wceq
    #
    vx
    cA
    wral
    #
    @5
    @15
    wceq
    @2
    @17
    @0
    @1
    @16
    vx
    cA
    @12
    cA
    wcel
    @1
    wa
    #
    cK
    @13
    @18
    @13
    cK
    vx
    cA
    cK
    ctop
    @7
    @7
    eqid
    #
    fvmpt2
    eqcomd
    unieqd
    ralimiaa
    adantl
    vx
    cA
    @4
    @14
    ixpeq2
    syl
    vy
    vx
    cA
    @9
    @14
    vx
    @8
    vx
    cA
    cK
    @6
    nffvmpt1
    nfuni
    vy
    @14
    nfcv
    @6
    @12
    wceq
    @8
    @13
    @6
    @12
    @7
    fveq2
    unieqd
    cbvixp
    syl6eqr
    @2
    @0
    cA
    ctop
    @7
    wf
    @10
    @11
    wceq
    vx
    cA
    ctop
    cK
    @7
    @19
    fmpt
    vy
    cA
    @7
    cJ
    cV
    ptunimpt.j
    ptuni
    sylan2b
    eqtrd
end
