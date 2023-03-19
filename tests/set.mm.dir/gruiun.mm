include "cgru.mm"
include "wcel.mm"
include "wral.mm"
include "ciun.mm"
include "wa.mm"
include "cmpt.mm"
include "crn.mm"
include "cuni.mm"
include "wf.mm"
include "wfn.mm"
include "wss.mm"
include "eqid.mm"
include "fnmpt.mm"
include "rnmptss.mm"
include "df-f.mm"
include "sylanbrc.mm"
include "gruurn.mm"
include "3expia.mm"
include "syl5com.mm"
include "dfiun3g.mm"
include "eleq1d.mm"
include "sylibrd.mm"
include "com12.mm"
include "3impia.mm"

theorem gruiun
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cU: class U
  let vy: setvar y
  let cF: class F

  disjoint U x
  disjoint A x
  disjoint U y
  disjoint x y
  disjoint A y
  disjoint B y
  disjoint F x
  disjoint F y
  assert |- ( ( U e. Univ /\ A e. U /\ A. x e. A B e. U ) -> U_ x e. A B e. U )

  proof
    cU
    cgru
    wcel
    #
    cA
    cU
    wcel
    #
    cB
    cU
    wcel
    vx
    cA
    wral
    #
    vx
    cA
    cB
    ciun
    #
    cU
    wcel
    #
    @2
    @0
    @1
    wa
    #
    @4
    @2
    @5
    vx
    cA
    cB
    cmpt
    #
    crn
    #
    cuni
    #
    cU
    wcel
    #
    @4
    @2
    cA
    cU
    @6
    wf
    #
    @5
    @9
    @2
    @6
    cA
    wfn
    @7
    cU
    wss
    @10
    vx
    cA
    cB
    @6
    cU
    @6
    eqid
    #
    fnmpt
    vx
    cA
    cB
    cU
    @6
    @11
    rnmptss
    cA
    cU
    @6
    df-f
    sylanbrc
    @0
    @1
    @10
    @9
    cA
    cU
    @6
    gruurn
    3expia
    syl5com
    @2
    @3
    @8
    cU
    vx
    cA
    cB
    cU
    dfiun3g
    eleq1d
    sylibrd
    com12
    3impia
end
