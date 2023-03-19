include "wcel.mm"
include "cmpt.mm"
include "wfn.mm"
include "w3a.mm"
include "cof.mm"
include "co.mm"
include "cv.mm"
include "csb.mm"
include "cvv.mm"
include "simp1.mm"
include "wa.mm"
include "wral.mm"
include "simpr.mm"
include "simpl2.mm"
include "eqid.mm"
include "mptfng.mm"
include "sylibr.mm"
include "nfcsb1v.mm"
include "nfel1.mm"
include "wceq.mm"
include "csbeq1a.mm"
include "eleq1d.mm"
include "rspc.mm"
include "sylc.mm"
include "simpl3.mm"
include "nfcv.mm"
include "cbvmpt.mm"
include "a1i.mm"
include "offval2.mm"
include "nfov.mm"
include "oveq12d.mm"
include "syl6eqr.mm"

theorem ofmpteq
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let cV: class V
  let va: setvar a

  disjoint A x
  disjoint R x
  disjoint A a
  disjoint a x
  disjoint V a
  disjoint B a
  disjoint C a
  disjoint R a
  assert |- ( ( A e. V /\ ( x e. A |-> B ) Fn A /\ ( x e. A |-> C ) Fn A ) -> ( ( x e. A |-> B ) oF R ( x e. A |-> C ) ) = ( x e. A |-> ( B R C ) ) )

  proof
    cA
    cV
    wcel
    #
    vx
    cA
    cB
    cmpt
    #
    cA
    wfn
    #
    vx
    cA
    cC
    cmpt
    #
    cA
    wfn
    #
    w3a
    #
    @1
    @3
    cR
    cof
    co
    va
    cA
    vx
    va
    cv
    #
    cB
    csb
    #
    vx
    @6
    cC
    csb
    #
    cR
    co
    #
    cmpt
    vx
    cA
    cB
    cC
    cR
    co
    #
    cmpt
    @5
    va
    cA
    @7
    @8
    cR
    @1
    @3
    cV
    cvv
    cvv
    @0
    @2
    @4
    simp1
    @5
    @6
    cA
    wcel
    #
    wa
    #
    @11
    cB
    cvv
    wcel
    #
    vx
    cA
    wral
    #
    @7
    cvv
    wcel
    #
    @5
    @11
    simpr
    #
    @12
    @2
    @14
    @0
    @2
    @4
    @11
    simpl2
    vx
    cA
    cB
    @1
    @1
    eqid
    mptfng
    sylibr
    @13
    @15
    vx
    @6
    cA
    vx
    @7
    cvv
    vx
    @6
    cB
    nfcsb1v
    #
    nfel1
    vx
    cv
    @6
    wceq
    #
    cB
    @7
    cvv
    vx
    @6
    cB
    csbeq1a
    #
    eleq1d
    rspc
    sylc
    @12
    @11
    cC
    cvv
    wcel
    #
    vx
    cA
    wral
    #
    @8
    cvv
    wcel
    #
    @16
    @12
    @4
    @21
    @0
    @2
    @4
    @11
    simpl3
    vx
    cA
    cC
    @3
    @3
    eqid
    mptfng
    sylibr
    @20
    @22
    vx
    @6
    cA
    vx
    @8
    cvv
    vx
    @6
    cC
    nfcsb1v
    #
    nfel1
    @18
    cC
    @8
    cvv
    vx
    @6
    cC
    csbeq1a
    #
    eleq1d
    rspc
    sylc
    @1
    va
    cA
    @7
    cmpt
    wceq
    @5
    vx
    va
    cA
    cB
    @7
    va
    cB
    nfcv
    @17
    @19
    cbvmpt
    a1i
    @3
    va
    cA
    @8
    cmpt
    wceq
    @5
    vx
    va
    cA
    cC
    @8
    va
    cC
    nfcv
    @23
    @24
    cbvmpt
    a1i
    offval2
    vx
    va
    cA
    @10
    @9
    va
    @10
    nfcv
    vx
    @7
    @8
    cR
    @17
    vx
    cR
    nfcv
    @23
    nfov
    @18
    cB
    @7
    cC
    @8
    cR
    @19
    @24
    oveq12d
    cbvmpt
    syl6eqr
end
