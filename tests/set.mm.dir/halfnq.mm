include "cnq.mm"
include "wcel.mm"
include "c1q.mm"
include "cplq.mm"
include "co.mm"
include "crq.mm"
include "cfv.mm"
include "cmq.mm"
include "wceq.mm"
include "cv.mm"
include "wex.mm"
include "distrnq.mm"
include "1nq.mm"
include "addclnq.mm"
include "mp2an.mm"
include "recidnq.mm"
include "ax-mp.mm"
include "oveq12i.mm"
include "eqtri.mm"
include "oveq1i.mm"
include "oveq2i.mm"
include "mulassnq.mm"
include "mulcomnq.mm"
include "eqtr3i.mm"
include "recclnq.mm"
include "syl2anc.mm"
include "mulidnq.mm"
include "mp2b.mm"
include "3eqtr3i.mm"
include "syl5eq.mm"
include "ovex.mm"
include "oveq12.mm"
include "anidms.mm"
include "eqeq1d.mm"
include "spcev.mm"
include "syl.mm"

theorem halfnq
  let vx: setvar x
  let cA: class A

  disjoint A x
  assert |- ( A e. Q. -> E. x ( x +Q x ) = A )

  proof
    cA
    cnq
    wcel
    #
    cA
    c1q
    c1q
    cplq
    co
    #
    crq
    cfv
    #
    cmq
    co
    #
    @3
    cplq
    co
    #
    cA
    wceq
    #
    vx
    cv
    #
    @6
    cplq
    co
    #
    cA
    wceq
    #
    vx
    wex
    @0
    @4
    cA
    c1q
    cmq
    co
    #
    cA
    cA
    @2
    @2
    cplq
    co
    #
    cmq
    co
    @4
    @9
    cA
    @2
    @2
    distrnq
    @10
    c1q
    cA
    cmq
    @1
    @10
    cmq
    co
    #
    @2
    cmq
    co
    #
    @1
    @2
    cmq
    co
    #
    @10
    c1q
    @11
    @1
    @2
    cmq
    @11
    @13
    @13
    cplq
    co
    @1
    @1
    @2
    @2
    distrnq
    @13
    c1q
    @13
    c1q
    cplq
    @1
    cnq
    wcel
    #
    @13
    c1q
    wceq
    c1q
    cnq
    wcel
    #
    @15
    @14
    1nq
    1nq
    c1q
    c1q
    addclnq
    mp2an
    #
    @1
    recidnq
    ax-mp
    #
    @17
    oveq12i
    eqtri
    oveq1i
    @10
    @13
    cmq
    co
    #
    @10
    c1q
    cmq
    co
    #
    @12
    @10
    @13
    c1q
    @10
    cmq
    @17
    oveq2i
    @10
    @1
    cmq
    co
    #
    @2
    cmq
    co
    @18
    @12
    @10
    @1
    @2
    mulassnq
    @20
    @11
    @2
    cmq
    @10
    @1
    mulcomnq
    oveq1i
    eqtr3i
    @14
    @10
    cnq
    wcel
    #
    @19
    @10
    wceq
    @16
    @14
    @2
    cnq
    wcel
    #
    @22
    @21
    @1
    recclnq
    #
    @23
    @2
    @2
    addclnq
    syl2anc
    @10
    mulidnq
    mp2b
    3eqtr3i
    @17
    3eqtr3i
    oveq2i
    eqtr3i
    cA
    mulidnq
    syl5eq
    @8
    @5
    vx
    @3
    cA
    @2
    cmq
    ovex
    @6
    @3
    wceq
    #
    @7
    @4
    cA
    @24
    @7
    @4
    wceq
    @6
    @3
    @6
    @3
    cplq
    oveq12
    anidms
    eqeq1d
    spcev
    syl
end
