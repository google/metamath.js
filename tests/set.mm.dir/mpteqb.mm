include "wcel.mm"
include "wral.mm"
include "cvv.mm"
include "cmpt.mm"
include "wceq.mm"
include "wb.mm"
include "elex.mm"
include "ralimi.mm"
include "wfn.mm"
include "fneq1.mm"
include "eqid.mm"
include "mptfng.mm"
include "3bitr4g.mm"
include "biimpd.mm"
include "wa.mm"
include "r19.26.mm"
include "wi.mm"
include "nfmpt1.mm"
include "nfeq.mm"
include "cv.mm"
include "cfv.mm"
include "simpll.mm"
include "fveq1d.mm"
include "fvmpt2.mm"
include "ad2ant2lr.mm"
include "ad2ant2l.mm"
include "3eqtr3d.mm"
include "exp31.mm"
include "ralrimi.mm"
include "ralim.mm"
include "syl.mm"
include "syl5bir.mm"
include "expd.mm"
include "mpdd.mm"
include "com12.mm"
include "mpteq12.mm"
include "mpan.mm"
include "impbid1.mm"

theorem mpteqb
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cV: class V

  disjoint A x
  assert |- ( A. x e. A B e. V -> ( ( x e. A |-> B ) = ( x e. A |-> C ) <-> A. x e. A B = C ) )

  proof
    cB
    cV
    wcel
    #
    vx
    cA
    wral
    cB
    cvv
    wcel
    #
    vx
    cA
    wral
    #
    vx
    cA
    cB
    cmpt
    #
    vx
    cA
    cC
    cmpt
    #
    wceq
    #
    cB
    cC
    wceq
    #
    vx
    cA
    wral
    #
    wb
    @0
    @1
    vx
    cA
    cB
    cV
    elex
    ralimi
    @2
    @5
    @7
    @5
    @2
    @7
    @5
    @2
    cC
    cvv
    wcel
    #
    vx
    cA
    wral
    #
    @7
    @5
    @2
    @9
    @5
    @3
    cA
    wfn
    @4
    cA
    wfn
    @2
    @9
    cA
    @3
    @4
    fneq1
    vx
    cA
    cB
    @3
    @3
    eqid
    #
    mptfng
    vx
    cA
    cC
    @4
    @4
    eqid
    #
    mptfng
    3bitr4g
    biimpd
    @5
    @2
    @9
    @7
    @2
    @9
    wa
    @1
    @8
    wa
    #
    vx
    cA
    wral
    #
    @5
    @7
    @1
    @8
    vx
    cA
    r19.26
    @5
    @12
    @6
    wi
    #
    vx
    cA
    wral
    @13
    @7
    wi
    @5
    @14
    vx
    cA
    vx
    @3
    @4
    vx
    cA
    cB
    nfmpt1
    vx
    cA
    cC
    nfmpt1
    nfeq
    @5
    vx
    cv
    #
    cA
    wcel
    #
    @12
    @6
    @5
    @16
    wa
    @12
    wa
    #
    @15
    @3
    cfv
    #
    @15
    @4
    cfv
    #
    cB
    cC
    @17
    @15
    @3
    @4
    @5
    @16
    @12
    simpll
    fveq1d
    @16
    @1
    @18
    cB
    wceq
    @5
    @8
    vx
    cA
    cB
    cvv
    @3
    @10
    fvmpt2
    ad2ant2lr
    @16
    @8
    @19
    cC
    wceq
    @5
    @1
    vx
    cA
    cC
    cvv
    @4
    @11
    fvmpt2
    ad2ant2l
    3eqtr3d
    exp31
    ralrimi
    @12
    @6
    vx
    cA
    ralim
    syl
    syl5bir
    expd
    mpdd
    com12
    cA
    cA
    wceq
    @7
    @5
    cA
    eqid
    vx
    cA
    cB
    cA
    cC
    mpteq12
    mpan
    impbid1
    syl
end
