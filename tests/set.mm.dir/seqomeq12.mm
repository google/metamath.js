include "wceq.mm"
include "wa.mm"
include "com.mm"
include "cvv.mm"
include "cv.mm"
include "csuc.mm"
include "co.mm"
include "cop.mm"
include "cmpt2.mm"
include "c0.mm"
include "cid.mm"
include "cfv.mm"
include "crdg.mm"
include "cima.mm"
include "cseqom.mm"
include "oveq.mm"
include "opeq2d.mm"
include "mpt2eq3dv.mm"
include "fveq2.mm"
include "rdgeq12.mm"
include "syl2an.mm"
include "imaeq1d.mm"
include "df-seqom.mm"
include "3eqtr4g.mm"

theorem seqomeq12
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let va: setvar a
  let vb: setvar b


  assert |- ( ( A = B /\ C = D ) -> seqom ( A , C ) = seqom ( B , D ) )

  proof
    cA
    cB
    wceq
    #
    cC
    cD
    wceq
    #
    wa
    #
    va
    vb
    com
    cvv
    va
    cv
    #
    csuc
    #
    @3
    vb
    cv
    #
    cA
    co
    #
    cop
    #
    cmpt2
    #
    c0
    cC
    cid
    cfv
    #
    cop
    #
    crdg
    #
    com
    cima
    va
    vb
    com
    cvv
    @4
    @3
    @5
    cB
    co
    #
    cop
    #
    cmpt2
    #
    c0
    cD
    cid
    cfv
    #
    cop
    #
    crdg
    #
    com
    cima
    cA
    cC
    cseqom
    cB
    cD
    cseqom
    @2
    @11
    @17
    com
    @0
    @8
    @14
    wceq
    @10
    @16
    wceq
    @11
    @17
    wceq
    @1
    @0
    va
    vb
    com
    cvv
    @7
    @13
    @0
    @6
    @12
    @4
    @3
    @5
    cA
    cB
    oveq
    opeq2d
    mpt2eq3dv
    @1
    @9
    @15
    c0
    cC
    cD
    cid
    fveq2
    opeq2d
    @10
    @16
    @8
    @14
    rdgeq12
    syl2an
    imaeq1d
    vb
    va
    cA
    cC
    df-seqom
    vb
    va
    cB
    cD
    df-seqom
    3eqtr4g
end
