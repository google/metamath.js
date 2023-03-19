include "cv.mm"
include "wceq.mm"
include "wi.mm"
include "wal.mm"
include "cmpt.mm"
include "wcel.mm"
include "wa.mm"
include "w3a.mm"
include "cfv.mm"
include "simp2.mm"
include "fveq1d.mm"
include "wrex.mm"
include "risset.mm"
include "cvv.mm"
include "elex.mm"
include "nfa1.mm"
include "nfv.mm"
include "nffvmpt1.mm"
include "nfeq1.mm"
include "nfim.mm"
include "simprl.mm"
include "simplr.mm"
include "simprr.mm"
include "eqeltrd.mm"
include "eqid.mm"
include "fvmpt2.mm"
include "syl2anc.mm"
include "simpll.mm"
include "fveq2d.mm"
include "3eqtr3d.mm"
include "exp43.mm"
include "a2i.mm"
include "com23.mm"
include "sps.mm"
include "rexlimd.mm"
include "syl7.mm"
include "syl5bi.mm"
include "imp32.mm"
include "3adant2.mm"
include "eqtrd.mm"

theorem fvmptt
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cF: class F
  let cV: class V

  disjoint A x
  disjoint C x
  disjoint D x
  assert |- ( ( A. x ( x = A -> B = C ) /\ F = ( x e. D |-> B ) /\ ( A e. D /\ C e. V ) ) -> ( F ` A ) = C )

  proof
    vx
    cv
    #
    cA
    wceq
    #
    cB
    cC
    wceq
    #
    wi
    #
    vx
    wal
    #
    cF
    vx
    cD
    cB
    cmpt
    #
    wceq
    #
    cA
    cD
    wcel
    #
    cC
    cV
    wcel
    #
    wa
    #
    w3a
    #
    cA
    cF
    cfv
    cA
    @5
    cfv
    #
    cC
    @10
    cA
    cF
    @5
    @4
    @6
    @9
    simp2
    fveq1d
    @4
    @9
    @11
    cC
    wceq
    #
    @6
    @4
    @7
    @8
    @12
    @7
    @1
    vx
    cD
    wrex
    #
    @4
    @8
    @12
    wi
    vx
    cA
    cD
    risset
    @8
    cC
    cvv
    wcel
    #
    @4
    @13
    @12
    cC
    cV
    elex
    @4
    @1
    @14
    @12
    wi
    #
    vx
    cD
    @3
    vx
    nfa1
    @14
    @12
    vx
    @14
    vx
    nfv
    vx
    @11
    cC
    vx
    cD
    cB
    cA
    nffvmpt1
    nfeq1
    nfim
    @3
    @0
    cD
    wcel
    #
    @1
    @15
    wi
    wi
    vx
    @3
    @1
    @16
    @15
    @1
    @2
    @16
    @15
    wi
    @1
    @2
    @16
    @14
    @12
    @1
    @2
    wa
    #
    @16
    @14
    wa
    #
    wa
    #
    @0
    @5
    cfv
    #
    cB
    @11
    cC
    @19
    @16
    cB
    cvv
    wcel
    @20
    cB
    wceq
    @17
    @16
    @14
    simprl
    @19
    cB
    cC
    cvv
    @1
    @2
    @18
    simplr
    #
    @17
    @16
    @14
    simprr
    eqeltrd
    vx
    cD
    cB
    cvv
    @5
    @5
    eqid
    fvmpt2
    syl2anc
    @19
    @0
    cA
    @5
    @1
    @2
    @18
    simpll
    fveq2d
    @21
    3eqtr3d
    exp43
    a2i
    com23
    sps
    rexlimd
    syl7
    syl5bi
    imp32
    3adant2
    eqtrd
end
